//! Exact Rust replacement for analyze.py's CUDA-sweep postprocessing.
//! Python remains the reference; outputs are isolated under --output-dir.
use collatz_search::pinned_lean_toolchain;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

type Result<T> = std::result::Result<T, String>;
const ROOT: &str = env!("CARGO_MANIFEST_DIR");
const SAMPLE_FUEL: u64 = 2_000_000;
const CYCLE_FUEL: u64 = 2_000_000;
const LEAN_N: u64 = 100_000;
const LEAN_FUEL: u64 = 200_000;

#[derive(Clone, Debug)]
struct InventoryCycle {
    minimum: BigUint,
    odd_length: u64,
    halvings: u64,
    length: u64,
    maximum: BigUint,
    members: Vec<BigUint>,
}
#[derive(Clone, Debug)]
struct Sweep {
    a: BigUint,
    c: BigInt,
    n: BigUint,
    tau: BigUint,
    cycles: Vec<InventoryCycle>,
    counts: Vec<BigUint>,
    escape: BigUint,
    oddsteps: BigUint,
    halvings: BigUint,
    samples: Vec<BigUint>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Verdict {
    Cycle(BigUint),
    Huge(BigUint),
    Undecided,
}
impl Verdict {
    fn json(&self) -> Value {
        match self {
            Self::Cycle(n) => json!(["cycle", n.to_string()]),
            Self::Huge(n) => json!(["huge", n.to_string()]),
            Self::Undecided => json!(["undecided"]),
        }
    }
}

fn scalar(value: &Value) -> Result<String> {
    match value {
        Value::Number(n) => Ok(n.to_string()),
        Value::String(s) => Ok(s.clone()),
        _ => Err("expected an exact integer number or decimal string".into()),
    }
}
fn natural(value: &Value) -> Result<BigUint> {
    scalar(value)?
        .parse()
        .map_err(|_| "expected a nonnegative integer".into())
}
fn signed(value: &Value) -> Result<BigInt> {
    scalar(value)?
        .parse()
        .map_err(|_| "expected an integer".into())
}
fn bounded(value: &Value) -> Result<u64> {
    natural(value)?
        .to_u64()
        .ok_or_else(|| "integer exceeds bounded u64 loop counter".into())
}
fn array(value: &Value) -> Result<&Vec<Value>> {
    value
        .as_array()
        .ok_or_else(|| "expected a JSON array".into())
}
fn naturals(value: &Value) -> Result<Vec<BigUint>> {
    array(value)?.iter().map(natural).collect()
}
fn parse_sweep(value: &Value) -> Result<Sweep> {
    let cycles = array(&value["cycles"])?
        .iter()
        .map(|cy| {
            Ok(InventoryCycle {
                minimum: natural(&cy["min"])?,
                odd_length: bounded(&cy["k"])?,
                halvings: bounded(&cy["H"])?,
                length: bounded(&cy["len"])?,
                maximum: natural(&cy["max"])?,
                members: naturals(&cy["members"])?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let row = Sweep {
        a: natural(&value["a"])?,
        c: signed(&value["c"])?,
        n: natural(&value["N"])?,
        tau: natural(&value["tau"])?,
        cycles,
        counts: naturals(&value["passB"]["counts"])?,
        escape: natural(&value["passB"]["escape"])?,
        oddsteps: natural(&value["passB"]["oddsteps"])?,
        halvings: natural(&value["passB"]["halvings"])?,
        samples: naturals(&value["passB"]["samples"])?,
    };
    if row.a.is_zero() || !row.a.bit(0) || row.n < BigUint::from(2_u32) {
        return Err("positive odd multiplier and N>=2 required".into());
    }
    if row.c <= BigInt::zero() && !(row.a == BigUint::from(3_u32) && row.c == BigInt::from(-1)) {
        return Err(
            "Lean exporter supports positive c, and the special (3,-1) variant only".into(),
        );
    }
    if row.counts.len() != row.cycles.len() {
        return Err("passB counts and cycle inventory lengths differ".into());
    }
    let distinct: BTreeSet<_> = row.cycles.iter().map(|cycle| &cycle.minimum).collect();
    if distinct.len() != row.cycles.len() {
        return Err("cycle inventory contains duplicate minima".into());
    }
    Ok(row)
}
fn read_sweeps(path: &Path) -> Result<Vec<Sweep>> {
    let input = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut rows = Vec::new();
    let mut keys = BTreeSet::new();
    for (line, text) in input.lines().enumerate() {
        let value: Value =
            serde_json::from_str(text).map_err(|e| format!("line {}: {e}", line + 1))?;
        let row = parse_sweep(&value).map_err(|e| format!("line {}: {e}", line + 1))?;
        if !keys.insert((row.a.clone(), row.c.clone())) {
            return Err(format!("duplicate variant ({},{})", row.a, row.c));
        }
        rows.push(row);
    }
    if rows.is_empty() {
        return Err("empty sweep input".into());
    }
    Ok(rows)
}

/// Exact accelerated odd step. Nonpositive numerators are rejected explicitly.
fn odd_step(n: &BigUint, a: &BigUint, c: &BigInt) -> Result<(BigUint, u64, BigUint)> {
    let numerator = (BigInt::from(a * n) + c)
        .to_biguint()
        .ok_or_else(|| "odd step left the positive integers".to_owned())?;
    let h = numerator
        .trailing_zeros()
        .ok_or_else(|| "odd step reached zero".to_owned())?;
    let shift = usize::try_from(h).map_err(|_| "halving count exceeds platform shift range")?;
    Ok((&numerator >> shift, h, numerator))
}
fn classify_big(
    start: &BigUint,
    a: &BigUint,
    c: &BigInt,
    mins: &BTreeSet<BigUint>,
    cap_steps: u64,
    cap_value: &BigUint,
) -> Result<Verdict> {
    if start.is_zero() {
        return Err("classification requires a positive start".into());
    }
    let mut n = start.clone();
    for _ in 0..cap_steps {
        if mins.contains(&n) {
            return Ok(Verdict::Cycle(n));
        }
        if &n > cap_value {
            return Ok(Verdict::Huge(n));
        }
        n = odd_step(&n, a, c)?.0;
    }
    Ok(Verdict::Undecided)
}

/// Canonical directed cycle: rotate the minimum to the front, never reverse.
fn canonical_cycle(members: &[BigUint]) -> Vec<BigUint> {
    let Some((minimum_index, _)) = members.iter().enumerate().min_by_key(|(_, n)| *n) else {
        return Vec::new();
    };
    members[minimum_index..]
        .iter()
        .chain(&members[..minimum_index])
        .cloned()
        .collect()
}
fn validate_cycle(row: &Sweep, cycle: &InventoryCycle, cap_steps: u64) -> Result<Value> {
    if cycle.odd_length == 0 || cycle.odd_length > cap_steps {
        return Err(format!(
            "cycle odd length {} is outside 1..={cap_steps}",
            cycle.odd_length
        ));
    }
    if cycle.minimum.is_zero() || !cycle.minimum.bit(0) {
        return Err("cycle minimum must be positive and odd".into());
    }
    let mut n = cycle.minimum.clone();
    let mut members = Vec::new();
    let mut total_halvings = 0_u64;
    let mut maximum = n.clone();
    let mut power_two = BigUint::one();
    let mut power_a = BigUint::one();
    let mut weight = BigUint::zero();
    for index in 0..cycle.odd_length {
        members.push(n.clone());
        let (next, h, numerator) = odd_step(&n, &row.a, &row.c)?;
        maximum = maximum.max(numerator);
        total_halvings = total_halvings
            .checked_add(h)
            .ok_or("cycle halving counter overflow")?;
        // W_{i+1}=a*W_i+2^(h_0+...+h_{i-1}), with no floating arithmetic.
        weight *= &row.a;
        weight += &power_two;
        power_two <<= usize::try_from(h).map_err(|_| "halving count exceeds shift range")?;
        power_a *= &row.a;
        n = next;
        if n == cycle.minimum && index + 1 < cycle.odd_length {
            return Err("recorded cycle length is not its primitive period".into());
        }
    }
    if n != cycle.minimum {
        return Err("recorded cycle does not close within its declared odd period".into());
    }
    let canonical = canonical_cycle(&members);
    if canonical.first() != Some(&cycle.minimum) {
        return Err("recorded cycle minimum is not canonical".into());
    }
    let ordinary_length = cycle
        .odd_length
        .checked_add(total_halvings)
        .ok_or("ordinary cycle length overflow")?;
    if total_halvings != cycle.halvings
        || ordinary_length != cycle.length
        || maximum != cycle.maximum
    {
        return Err(
            "recorded cycle halving count, ordinary length, or maximum disagrees with exact replay"
                .into(),
        );
    }
    let prefix: Vec<_> = members.iter().take(24).cloned().collect();
    if prefix != cycle.members {
        return Err("recorded cycle member prefix disagrees with exact canonical replay".into());
    }
    let denominator = BigInt::from(power_two) - BigInt::from(power_a);
    if BigInt::from(cycle.minimum.clone()) * &denominator != &row.c * BigInt::from(weight) {
        return Err("exact cycle-equation identity failed".into());
    }
    Ok(
        json!({"a": row.a.to_string(), "c": row.c.to_string(), "min": cycle.minimum.to_string(),
              "k": cycle.odd_length, "H": total_halvings, "len": ordinary_length,
              "max": maximum.to_string(), "D": denominator.to_string(),
              "members": members.iter().map(ToString::to_string).collect::<Vec<_>>()}),
    )
}

fn sorted_mins(row: &Sweep) -> Vec<BigUint> {
    let mut mins: Vec<_> = row.cycles.iter().map(|c| c.minimum.clone()).collect();
    mins.sort();
    mins
}
fn structures(rows: &[Sweep], sample_fuel: u64, cap: &BigUint) -> Result<()> {
    let index: BTreeMap<_, _> = rows
        .iter()
        .map(|r| ((r.a.clone(), r.c.clone()), r))
        .collect();
    let get = |a: u32, c: i32| -> Result<&Sweep> {
        index
            .get(&(BigUint::from(a), BigInt::from(c)))
            .copied()
            .ok_or_else(|| format!("structural check requires variant ({a},{c})"))
    };
    for (a, c, expected) in [
        (3, 1, vec![1_u32]),
        (3, -1, vec![1, 5, 17]),
        (5, 1, vec![1, 13, 17]),
        (7, 1, vec![1]),
        (3, 3, vec![3]),
    ] {
        let wanted: Vec<_> = expected.into_iter().map(BigUint::from).collect();
        if sorted_mins(get(a, c)?) != wanted {
            return Err(format!("inventory structure mismatch for ({a},{c})"));
        }
    }
    let belaga: BTreeSet<_> = sorted_mins(get(3, 5)?).into_iter().collect();
    if ![1_u32, 5, 19, 23]
        .into_iter()
        .all(|n| belaga.contains(&BigUint::from(n)))
    {
        return Err("(3,5) inventory is missing an expected minimum".into());
    }
    for row in rows {
        if [3_u32, 7, 15]
            .into_iter()
            .any(|a| row.a == BigUint::from(a))
            && row.c > BigInt::zero()
        {
            let c = row.c.to_biguint().unwrap();
            let minima = sorted_mins(row).into_iter().collect();
            if !matches!(
                classify_big(&c, &row.a, &row.c, &minima, sample_fuel, cap)?,
                Verdict::Cycle(_)
            ) {
                return Err(format!(
                    "universal-cycle structural check unresolved for ({},{})",
                    row.a, row.c
                ));
            }
        }
    }
    for (a, left_c, right_c) in [(3, 9, 3), (3, 15, 5), (9, 3, 1), (15, 3, 1)] {
        let scaled: Vec<_> = sorted_mins(get(a, right_c)?)
            .into_iter()
            .map(|m| m * 3_u32)
            .collect();
        if sorted_mins(get(a, left_c)?) != scaled {
            return Err(format!("scaling inventory mismatch for ({a},{left_c})"));
        }
    }
    for c in [1, -1] {
        let (halvings, _, _) = drift_row(get(3, c)?)?;
        if !halvings.is_finite() || (halvings - 2.0).abs() >= 0.05 {
            return Err(format!("drift sanity check failed for (3,{c})"));
        }
    }
    Ok(())
}

fn ratio(numerator: &BigUint, denominator: &BigUint) -> Result<f64> {
    if denominator.is_zero() {
        return Ok(f64::NAN);
    }
    if let (Some(n), Some(d)) = (numerator.to_f64(), denominator.to_f64())
        && n.is_finite()
        && d.is_finite()
    {
        return Ok(n / d);
    }
    // Keep high bits and the exponent separately for huge reporting counters.
    let n_shift = numerator.bits().saturating_sub(53);
    let d_shift = denominator.bits().saturating_sub(53);
    let n = (numerator
        >> usize::try_from(n_shift).map_err(|_| "counter too large for platform")?)
    .to_f64()
    .unwrap();
    let d = (denominator
        >> usize::try_from(d_shift).map_err(|_| "counter too large for platform")?)
    .to_f64()
    .unwrap();
    let exponent = i128::from(n_shift) - i128::from(d_shift);
    let result = n / d * (2_f64).powf(exponent as f64);
    if !result.is_finite() {
        return Err("reporting ratio exceeds finite f64 range".into());
    }
    Ok(result)
}
fn log_uint(n: &BigUint) -> Result<f64> {
    if n.is_zero() {
        return Err("logarithm of zero in drift report".into());
    }
    if let Some(x) = n.to_f64().filter(|x| x.is_finite()) {
        return Ok(x.ln());
    }
    let shift = n.bits().saturating_sub(53);
    let high = (n >> usize::try_from(shift).map_err(|_| "multiplier too large for platform")?)
        .to_f64()
        .unwrap();
    Ok(high.ln() + shift as f64 * 2_f64.ln())
}
fn drift_row(row: &Sweep) -> Result<(f64, f64, f64)> {
    let hpo = ratio(&row.halvings, &row.oddsteps)?;
    let log_a = log_uint(&row.a)?;
    Ok((hpo, log_a - hpo * 2_f64.ln(), log_a - 2.0 * 2_f64.ln()))
}
fn four(n: f64, signed: bool) -> String {
    (if signed {
        format!("{n:+.4}")
    } else {
        format!("{n:.4}")
    })
    .replace("NaN", "nan")
}
fn summary(rows: &[Sweep]) -> Result<String> {
    let mut lines = vec!["| a | c | N swept | cycles (odd minima) | converged % | escaped-window % | E[halv/odd step] | drift/odd step (meas) | drift (pred ln a - 2 ln 2) |".to_owned(),
        "|---|---|---------|--------------------|-------------|------------------|------------------|----------------------|-----------------------------|".to_owned()];
    for row in rows {
        let nodd = &row.n >> 1_usize;
        let converged: BigUint = row.counts.iter().cloned().sum();
        let (hpo, dm, dp) = drift_row(row)?;
        let mut mins = row
            .cycles
            .iter()
            .map(|c| c.minimum.to_string())
            .collect::<Vec<_>>()
            .join(",");
        if mins.is_empty() {
            mins = "(none)".to_owned();
        }
        if mins.len() > 40 {
            mins.truncate(37);
            mins.push_str("...");
        }
        lines.push(format!(
            "| {} | {} | 2^{} | {}: {} | {} | {} | {} | {} | {} |",
            row.a,
            row.c,
            row.n.bits() - 1,
            row.cycles.len(),
            mins,
            four(ratio(&(converged * 100_u32), &nodd)?, false),
            four(ratio(&(&row.escape * 100_u32), &nodd)?, false),
            four(hpo, false),
            four(dm, true),
            four(dp, true)
        ));
    }
    Ok(lines.join("\n") + "\n")
}

const HEADER: &str = r#"/-
  CollatzCerts.lean — GENERATED by Rust analyze from CUDA sweep results.
  Certificates:
    (i)  every discovered cycle is a genuine cycle       (`decide` up to 512 steps,
         `native_decide` for longer cycles)
    (ii) for each variant, EVERY n in [1, 100000] either reaches the
         cycle inventory or exceeds the u64 window tau    (`native_decide`)
  Check with:  lean CollatzCerts.lean    (using the repository's pinned toolchain)
-/

-- long cycles unfold ~10 elaborator frames per step; default depth 512 fails at len ≥ ~40
set_option maxRecDepth 100000

def T (a c n : Nat) : Nat := if n % 2 = 1 then a * n + c else n / 2

/-- 3x-1 variant (the one negative-c system in the sweep). -/
def Tm1 (n : Nat) : Nat := if n % 2 = 1 then 3 * n - 1 else n / 2

def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | k + 1, x => iterN f k (f x)

/-- Does the orbit of n hit `mins` (or leave the window tau) within `fuel` steps? -/
def orbHits (f : Nat → Nat) (mins : List Nat) (tau : Nat) : Nat → Nat → Bool
  | _, 0     => false
  | n, k + 1 =>
    if mins.contains n then true
    else if tau < n then true
    else orbHits f mins tau (f n) k

/-- Check every start in [1, i+left) ... driver: checkFrom f mins tau fuel 1 N. -/
def checkFrom (f : Nat → Nat) (mins : List Nat) (tau fuel : Nat) : Nat → Nat → Bool
  | _, 0        => true
  | i, left + 1 =>
    if orbHits f mins tau i fuel then checkFrom f mins tau fuel (i + 1) left
    else false
"#;
fn lname(row: &Sweep) -> String {
    format!(
        "a{}_c{}",
        row.a,
        if row.c == BigInt::from(-1) {
            "m1".into()
        } else {
            row.c.to_string()
        }
    )
}
fn certificate(rows: &[Sweep]) -> String {
    let mut certs = vec![HEADER.to_owned()];
    for row in rows {
        let function = if row.c == BigInt::from(-1) {
            "Tm1".to_owned()
        } else {
            format!("(T {} {})", row.a, row.c)
        };
        certs.push(format!("\n-- ==== variant a={}, c={} ====", row.a, row.c));
        for cycle in &row.cycles {
            let tactic = if cycle.length <= 512 {
                "decide"
            } else {
                "native_decide"
            };
            certs.push(format!(
                "theorem cyc_{}_m{} : iterN {} {} {} = {} := by {}",
                lname(row),
                cycle.minimum,
                function,
                cycle.length,
                cycle.minimum,
                cycle.minimum,
                tactic
            ));
        }
        let mins = row
            .cycles
            .iter()
            .map(|c| c.minimum.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        certs.push(format!(
            "theorem range_{} : checkFrom {} [{}] {} {} 1 {} = true := by native_decide",
            lname(row),
            function,
            mins,
            row.tau,
            LEAN_FUEL,
            LEAN_N
        ));
    }
    certs.push("\n#print axioms range_a3_c1".into());
    certs.push("#print axioms cyc_a3_c1_m1".into());
    certs.join("\n") + "\n"
}
fn analyze(rows: &[Sweep], sample_fuel: u64, cycle_fuel: u64, cap: &BigUint) -> Result<Value> {
    let mut samples = Vec::new();
    let mut cycles = Vec::new();
    for row in rows {
        let minima = sorted_mins(row).into_iter().collect();
        for start in &row.samples {
            let verdict = classify_big(start, &row.a, &row.c, &minima, sample_fuel, cap)?;
            if row.a <= BigUint::from(3_u32) && !matches!(verdict, Verdict::Cycle(_)) {
                return Err(format!(
                    "a<=3 sampled escape did not reconverge: a={}, c={}, start={}, verdict={verdict:?}",
                    row.a, row.c, start
                ));
            }
            samples.push(json!({"a":row.a.to_string(),"c":row.c.to_string(),"start":start.to_string(),"verdict":verdict.json()}));
        }
        for cycle in &row.cycles {
            cycles
                .push(validate_cycle(row, cycle, cycle_fuel).map_err(|e| {
                    format!("a={}, c={}, min={}: {e}", row.a, row.c, cycle.minimum)
                })?);
        }
    }
    structures(rows, sample_fuel, cap)?;
    Ok(
        json!({"schema":1,"implementation":"Rust","variants":rows.len(),"cycle_count":cycles.len(),
              "sample_count":samples.len(),"samples":samples,"cycles":cycles,
              "structure_checks":"passed","exact_cycle_equation_checks":"passed",
              "sample_fuel":sample_fuel,"cycle_fuel":cycle_fuel,"sample_value_cap":cap.to_string(),
              "integer_arithmetic":"arbitrary precision (BigUint/BigInt)",
              "scope":"sample validation and recorded-cycle replay; huge/fuel limits do not prove divergence"}),
    )
}

struct Options {
    raw: PathBuf,
    output: PathBuf,
    verify_lean: bool,
    check_only: bool,
    sample_fuel: u64,
    cycle_fuel: u64,
}
fn options() -> Result<Option<Options>> {
    let mut options = Options {
        raw: Path::new(ROOT).join("results/raw.jsonl"),
        output: Path::new(ROOT).join("results/analyze-rust"),
        verify_lean: false,
        check_only: false,
        sample_fuel: SAMPLE_FUEL,
        cycle_fuel: CYCLE_FUEL,
    };
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--raw" => options.raw = args.next().ok_or("--raw needs a path")?.into(),
            "--output-dir" => {
                options.output = args.next().ok_or("--output-dir needs a path")?.into()
            }
            "--verify-lean" => options.verify_lean = true,
            "--check-only" => options.check_only = true,
            "--sample-fuel" => {
                options.sample_fuel = args
                    .next()
                    .ok_or("--sample-fuel needs an integer")?
                    .parse()
                    .map_err(|_| "invalid sample fuel")?
            }
            "--cycle-fuel" => {
                options.cycle_fuel = args
                    .next()
                    .ok_or("--cycle-fuel needs an integer")?
                    .parse()
                    .map_err(|_| "invalid cycle fuel")?
            }
            "--help" | "-h" => {
                println!(
                    "Rust CUDA-sweep analysis\nUsage: analyze [--raw FILE] [--output-dir DIR] [--verify-lean] [--check-only]\n[--sample-fuel N] [--cycle-fuel N]\nDefault output: results/analyze-rust/{{CollatzCerts.lean,summary.md,analysis.json}}\nExact integer validation; generated Lean and floating drift display match analyze.py.\nPinned Lean toolchain: {}",
                    pinned_lean_toolchain()
                );
                return Ok(None);
            }
            _ => return Err(format!("unknown argument {arg}")),
        }
    }
    if options.check_only && options.verify_lean {
        return Err("--check-only and --verify-lean are mutually exclusive".into());
    }
    Ok(Some(options))
}
fn run() -> Result<()> {
    let Some(options) = options()? else {
        return Ok(());
    };
    if !options.check_only {
        let mut outputs = vec!["CollatzCerts.lean", "summary.md", "analysis.json"];
        if options.verify_lean {
            outputs.push("lean.log");
        }
        for name in outputs {
            if collatz_search::same_existing_file(&options.raw, &options.output.join(name))
                .map_err(|e| e.to_string())?
            {
                return Err(format!("output {name} must not overwrite input"));
            }
        }
    }
    let rows = read_sweeps(&options.raw)?;
    let cap = BigUint::from(10_u32).pow(60);
    let mut report = analyze(&rows, options.sample_fuel, options.cycle_fuel, &cap)?;
    report["certificate_status"] = json!("not_run");
    if !options.check_only {
        let source = certificate(&rows);
        let table = summary(&rows)?;
        fs::create_dir_all(&options.output).map_err(|e| e.to_string())?;
        let cert_path = options.output.join("CollatzCerts.lean");
        fs::write(&cert_path, &source).map_err(|e| e.to_string())?;
        fs::write(options.output.join("summary.md"), table).map_err(|e| e.to_string())?;
        report["certificate_sha256"] = json!(format!("{:x}", Sha256::digest(source.as_bytes())));
        report["certificate_file"] = json!(cert_path);
        fs::write(
            options.output.join("analysis.json"),
            serde_json::to_string_pretty(&report).unwrap() + "\n",
        )
        .map_err(|e| e.to_string())?;
        if options.verify_lean {
            let selector = format!("+{}", pinned_lean_toolchain());
            let checked = Command::new("lean")
                .arg(&selector)
                .arg(&cert_path)
                .output()
                .map_err(|e| e.to_string())?;
            let log = format!(
                "Command: lean {selector} {}\n{}{}",
                cert_path.display(),
                String::from_utf8_lossy(&checked.stdout),
                String::from_utf8_lossy(&checked.stderr)
            );
            fs::write(options.output.join("lean.log"), &log).map_err(|e| e.to_string())?;
            let proof_ok = collatz_search::lean_proof_succeeded(&checked);
            report["certificate_status"] = json!(if proof_ok { "verified" } else { "failed" });
            fs::write(
                options.output.join("analysis.json"),
                serde_json::to_string_pretty(&report).unwrap() + "\n",
            )
            .map_err(|e| e.to_string())?;
            if !proof_ok {
                return Err(format!(
                    "Lean rejected the generated certificate or reported an unfinished proof:\n{log}"
                ));
            }
        }
    }
    println!("{}",serde_json::to_string_pretty(&json!({"variants":rows.len(),"cycles":report["cycle_count"],
        "samples":report["sample_count"],"structure_checks":report["structure_checks"],
        "certificate_status":report["certificate_status"],"output_dir":if options.check_only { None } else { Some(options.output) }})).unwrap());
    Ok(())
}
fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn classifier_preserves_fuel_and_cap_boundary_semantics() {
        let a = BigUint::from(3_u32);
        let c = BigInt::from(1);
        let one = BigUint::one();
        let minima = BTreeSet::from([one.clone()]);
        assert_eq!(
            classify_big(&one, &a, &c, &minima, 0, &one).unwrap(),
            Verdict::Undecided
        );
        assert_eq!(
            classify_big(&one, &a, &c, &minima, 1, &BigUint::zero()).unwrap(),
            Verdict::Cycle(one.clone())
        );
        assert_eq!(
            classify_big(
                &BigUint::from(3_u32),
                &a,
                &c,
                &minima,
                1,
                &BigUint::from(2_u32)
            )
            .unwrap(),
            Verdict::Huge(BigUint::from(3_u32))
        );
        assert_eq!(
            classify_big(
                &BigUint::from(3_u32),
                &a,
                &c,
                &minima,
                1,
                &BigUint::from(3_u32)
            )
            .unwrap(),
            Verdict::Undecided
        );
        assert!(odd_step(&one, &one, &BigInt::from(-1)).is_err());
    }
    #[test]
    fn exact_json_integers_and_duplicate_inventory_rejection() {
        let decimal = "1".to_owned() + &"0".repeat(1000);
        let number: Value = serde_json::from_str(&decimal).unwrap();
        assert_eq!(natural(&number).unwrap().to_string(), decimal);
        assert!(natural(&json!(1.5)).is_err());
        let raw = fs::read_to_string(Path::new(ROOT).join("results/raw.jsonl")).unwrap();
        let mut row: Value = serde_json::from_str(raw.lines().next().unwrap()).unwrap();
        let duplicate = row["cycles"][0].clone();
        row["cycles"].as_array_mut().unwrap().push(duplicate);
        row["passB"]["counts"]
            .as_array_mut()
            .unwrap()
            .push(json!(0));
        assert!(parse_sweep(&row).unwrap_err().contains("duplicate minima"));
    }

    #[test]
    fn canonicalization_rotates_without_reversing() {
        let ints = |values: &[u32]| {
            values
                .iter()
                .copied()
                .map(BigUint::from)
                .collect::<Vec<_>>()
        };
        assert_eq!(canonical_cycle(&ints(&[7, 5])), ints(&[5, 7]));
        assert_eq!(
            canonical_cycle(&ints(&[37, 55, 41, 61, 91, 17, 25])),
            ints(&[17, 25, 37, 55, 41, 61, 91])
        );
    }
    #[test]
    fn arbitrary_precision_and_signed_cycle_equation() {
        let big = BigUint::one() << 4096_usize;
        let (next, h, numerator) = odd_step(
            &(&big - BigUint::one()),
            &BigUint::from(3_u32),
            &BigInt::one(),
        )
        .unwrap();
        assert_eq!(h, 1);
        assert_eq!(numerator, &big * 3_u32 - 2_u32);
        assert_eq!(next, (&big * 3_u32 - 2_u32) >> 1_usize);
        let rows = read_sweeps(&Path::new(ROOT).join("results/raw.jsonl")).unwrap();
        let minus = rows
            .iter()
            .find(|r| r.a == BigUint::from(3_u32) && r.c == BigInt::from(-1))
            .unwrap();
        assert_eq!(
            validate_cycle(minus, &minus.cycles[0], 100).unwrap()["D"],
            "-1"
        );
        let mut wrong = minus.cycles[0].clone();
        wrong.halvings += 1;
        assert!(validate_cycle(minus, &wrong, 100).is_err());
        let mut wrong = minus.cycles[1].clone();
        wrong.minimum = BigUint::from(7_u32);
        assert!(validate_cycle(minus, &wrong, 100).is_err());
        assert!(validate_cycle(minus, &minus.cycles[2], 1).is_err());
    }
    struct Temporary(PathBuf);
    impl Drop for Temporary {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    #[test]
    fn full_outputs_and_exact_results_match_current_python_reference() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let temp = Temporary(env::temp_dir().join(format!(
            "collatz-analyze-test-{}-{nonce}",
            std::process::id()
        )));
        fs::create_dir(&temp.0).unwrap();
        fs::create_dir(temp.0.join("results")).unwrap();
        fs::copy(
            Path::new(ROOT).join("results/raw.jsonl"),
            temp.0.join("results/raw.jsonl"),
        )
        .unwrap();
        let wrapper = r#"import json,runpy,sys
ns=runpy.run_path(sys.argv[1])
samples=[];cycles=[]
for r in ns['rows']:
    a,c=r['a'],r['c']; mins=[cy['min'] for cy in r['cycles']]
    for start in r['passB']['samples']:
        verdict=ns['classify_big'](start,a,c,mins)
        samples.append(dict(a=str(a),c=str(c),start=str(start),verdict=[verdict[0]]+[str(x) for x in verdict[1:]]))
    for cy in r['cycles']:
        members=[];n=cy['min']
        for _ in range(cy['k']):
            members.append(str(n));n=ns['odd_step'](n,a,c)
        cycles.append(dict(a=str(a),c=str(c),min=str(cy['min']),k=cy['k'],H=cy['H'],len=cy['len'],max=str(cy['max']),D=str(cy['D']),members=members))
with open('reference.json','w') as f:json.dump(dict(samples=samples,cycles=cycles),f)
"#;
        let checked = Command::new("python3")
            .arg("-c")
            .arg(wrapper)
            .arg(Path::new(ROOT).join("analyze.py"))
            .current_dir(&temp.0)
            .output()
            .unwrap();
        assert!(
            checked.status.success(),
            "{}",
            String::from_utf8_lossy(&checked.stderr)
        );
        let rows = read_sweeps(&temp.0.join("results/raw.jsonl")).unwrap();
        let rust = analyze(
            &rows,
            SAMPLE_FUEL,
            CYCLE_FUEL,
            &BigUint::from(10_u32).pow(60),
        )
        .unwrap();
        let reference: Value =
            serde_json::from_str(&fs::read_to_string(temp.0.join("reference.json")).unwrap())
                .unwrap();
        assert_eq!(rust["samples"], reference["samples"]);
        assert_eq!(rust["cycles"], reference["cycles"]);
        assert_eq!(
            summary(&rows).unwrap(),
            fs::read_to_string(temp.0.join("results/summary.md")).unwrap()
        );
        assert_eq!(
            certificate(&rows).replace("GENERATED by Rust analyze", "GENERATED by analyze.py"),
            fs::read_to_string(temp.0.join("CollatzCerts.lean")).unwrap()
        );
    }
}
