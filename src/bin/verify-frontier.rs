//! Exact Rust counterpart of verify_frontier.py.
//! Fuzz cases use a domain-separated SHAKE256 stream, not Python's MT stream.
//! All trajectory/formula arithmetic is BigUint; numeric count results agree
//! independently with the committed Python summary and Lean certificates.

use collatz_search::verify_helpers::{ShakeRng, accelerated, v2};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

type Check<T> = Result<T, String>;
const ROOT: &str = env!("CARGO_MANIFEST_DIR");
const FUZZ_DOMAIN: &str = "verify-frontier-rust-v1:20260704";
const MAX_INPUT_BYTES: u64 = 16 * 1024 * 1024;
const MAX_CYCLE_STEPS: usize = 100_000;
const MAX_ORBIT_BITS: u64 = 131_072;
const MAX_TOTAL_HALVINGS: u64 = 1_000_000;
const LEVELS: [(u32, u64); 3] = [(8, 219), (16, 58_651), (20, 910_596)];

#[derive(Clone, Deserialize)]
struct Cycle {
    min: u64,
    k: usize,
    #[serde(rename = "H")]
    h: u64,
    len: u64,
    max: u64,
    members: Vec<u64>,
}

#[derive(Clone, Deserialize)]
struct Variant {
    a: u64,
    c: i64,
    cycles: Vec<Cycle>,
}

#[derive(Debug, Serialize)]
struct GoodCount {
    level: u32,
    good: u64,
    total: u64,
    max_weight: u32,
    binomial_tail: String,
}

fn ensure(condition: bool, message: impl FnOnce() -> String) -> Check<()> {
    if condition { Ok(()) } else { Err(message()) }
}

fn checked_bits(n: &BigUint) -> Check<()> {
    ensure(n.bits() <= MAX_ORBIT_BITS, || {
        "trajectory exceeded validation bit limit".into()
    })
}

fn read_variants(path: &Path) -> Check<(Vec<Variant>, String)> {
    let meta = fs::metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    ensure(meta.is_file() && meta.len() <= MAX_INPUT_BYTES, || {
        "raw input must be a regular JSONL file of at most 16 MiB".into()
    })?;
    let bytes = fs::read(path).map_err(|e| e.to_string())?;
    let text = std::str::from_utf8(&bytes).map_err(|e| e.to_string())?;
    let mut rows = Vec::new();
    for (index, line) in text.lines().enumerate() {
        ensure(index < 1024 && line.len() <= 1024 * 1024, || {
            "JSONL dimension limit exceeded".into()
        })?;
        let row: Variant =
            serde_json::from_str(line).map_err(|e| format!("line {}: {e}", index + 1))?;
        ensure(row.a > 0 && row.c != 0 && row.cycles.len() <= 128, || {
            format!(
                "line {}: positive a, nonzero c, and at most 128 cycles required",
                index + 1
            )
        })?;
        for cy in &row.cycles {
            ensure(
                cy.min > 0 && cy.min % 2 == 1 && cy.k > 0 && cy.k <= MAX_CYCLE_STEPS,
                || {
                    format!(
                        "line {}: invalid positive odd minimum or cycle length",
                        index + 1
                    )
                },
            )?;
            ensure(
                cy.h <= MAX_TOTAL_HALVINGS && cy.members.len() == cy.k.min(24),
                || {
                    format!(
                        "line {}: invalid halving count or stored member prefix",
                        index + 1
                    )
                },
            )?;
        }
        rows.push(row);
    }
    ensure(!rows.is_empty(), || "empty raw JSONL input".into())?;
    Ok((rows, format!("{:x}", Sha256::digest(&bytes))))
}

/// Compute the same head-recursive S,W as Lean, iteratively to avoid stack overflow.
fn sw(a: &BigUint, c: &BigUint, x: &BigUint, n: usize) -> Check<(u64, BigUint)> {
    ensure(n <= MAX_CYCLE_STEPS, || {
        "orbit length exceeds validation bound".into()
    })?;
    let mut value = x.clone();
    let mut exponents = Vec::with_capacity(n);
    let mut sum = 0_u64;
    for _ in 0..n {
        let m = a * &value + c;
        checked_bits(&m)?;
        let h = v2(&m)?;
        sum = sum.checked_add(h).ok_or("halving counter overflow")?;
        ensure(sum <= MAX_TOTAL_HALVINGS, || {
            "total halvings exceed validation bound".into()
        })?;
        exponents.push(h);
        value = m >> h as usize;
    }
    let mut weight = BigUint::zero();
    let mut a_power = BigUint::one();
    for h in exponents.into_iter().rev() {
        weight = &a_power + (weight << h as usize);
        a_power *= a;
    }
    Ok((sum, weight))
}

fn iter_f(a: &BigUint, c: &BigUint, x: &BigUint, n: usize) -> Check<BigUint> {
    let mut value = x.clone();
    for _ in 0..n {
        value = accelerated(a, c, &value)?;
        checked_bits(&value)?;
    }
    Ok(value)
}

fn check_orbit_formula(a: BigUint, c: BigUint, x: BigUint, n: usize) -> Check<()> {
    let (s, w) = sw(&a, &c, &x, n)?;
    let lhs = iter_f(&a, &c, &x, n)? << s as usize;
    let rhs = a.pow(n as u32) * &x + c * w;
    ensure(lhs == rhs, || {
        format!("F1 orbit formula failed for a={a}, x={x}, n={n}")
    })
}

/// Replay exactly the claimed finite cycle length; never search until an unbounded return.
fn check_cycle(a: u64, c: u64, cy: &Cycle) -> Check<Vec<BigUint>> {
    ensure(
        cy.k > 0 && cy.k <= MAX_CYCLE_STEPS && cy.min > 0 && cy.min % 2 == 1,
        || "invalid cycle length or minimum".into(),
    )?;
    let a = BigUint::from(a);
    let c = BigUint::from(c);
    let first = BigUint::from(cy.min);
    let mut value = first.clone();
    let mut h_total = 0_u64;
    let mut peak = first.clone();
    let mut members = Vec::with_capacity(cy.k);
    for step in 0..cy.k {
        members.push(value.clone());
        let m = &a * &value + &c;
        checked_bits(&m)?;
        peak = peak.max(m.clone());
        let h = v2(&m)?;
        h_total = h_total
            .checked_add(h)
            .ok_or("cycle halving counter overflow")?;
        ensure(h_total <= MAX_TOTAL_HALVINGS, || {
            "cycle halving limit exceeded".into()
        })?;
        value = m >> h as usize;
        ensure(step + 1 == cy.k || value != first, || {
            "cycle returns before its stated primitive length".into()
        })?;
    }
    ensure(value == first, || {
        "cycle fails to return within its stated length".into()
    })?;
    ensure(h_total == cy.h && cy.len == cy.k as u64 + h_total, || {
        "cycle k/H/len mismatch".into()
    })?;
    ensure(
        peak == BigUint::from(cy.max) && members.iter().min() == Some(&first),
        || "cycle peak or minimum mismatch".into(),
    )?;
    ensure(
        cy.members.len() == cy.k.min(24)
            && cy
                .members
                .iter()
                .zip(&members)
                .all(|(stored, actual)| BigUint::from(*stored) == *actual),
        || "cycle stored member prefix mismatch".into(),
    )?;
    let (s, w) = sw(&a, &c, &first, cy.k)?;
    let power2 = BigUint::one() << h_total as usize;
    let power_a = a.pow(cy.k as u32);
    ensure(
        s == h_total && &first * &power2 == &power_a * &first + &c * &w,
        || "F2 additive cycle equation failed".into(),
    )?;
    ensure(power2 > power_a, || {
        "F2 cycle expansion inequality failed".into()
    })?;
    ensure(&first * (&power2 - &power_a) == &c * &w, || {
        "F2 subtractive cycle equation failed".into()
    })?;
    Ok(members)
}

fn t_step(a: &BigUint, c: &BigUint, n: &mut BigUint) {
    if n.bit(0) {
        *n = a * &*n + c;
    } else {
        *n >>= 1usize;
    }
}

fn u_step(n: &mut BigUint) {
    if n.bit(0) {
        *n *= 3_u32;
        *n += 1_u32;
    }
    *n >>= 1usize;
}

fn weight(k: u32, s: &BigUint) -> u32 {
    let mut value = s.clone();
    let mut w = 0;
    for _ in 0..k {
        w += u32::from(value.bit(0));
        u_step(&mut value);
    }
    w
}

fn uk(k: u32, n: &BigUint) -> BigUint {
    let mut value = n.clone();
    for _ in 0..k {
        u_step(&mut value);
    }
    value
}

fn binomial(n: u32, k: u32) -> BigUint {
    let mut value = BigUint::one();
    for i in 0..k {
        value *= n - i;
        value /= i + 1;
    }
    value
}

/// Direct enumeration of every residue using arbitrary-precision trajectory arithmetic.
fn count_good(k: u32) -> Check<GoodCount> {
    ensure(k > 0 && k <= 24, || "count level must lie in 1..=24".into())?;
    let total = 1_u64 << k;
    let modulus = BigUint::one() << k as usize;
    let powers: Vec<_> = (0..=k).map(|w| BigUint::from(3_u32).pow(w)).collect();
    let mut good = 0;
    for s in 0..total {
        let w = weight(k, &BigUint::from(s));
        good += u64::from(powers[w as usize] < modulus);
    }
    let max_weight = (0..=k)
        .filter(|w| powers[*w as usize] < modulus)
        .max()
        .unwrap();
    let tail: BigUint = (0..=max_weight).map(|w| binomial(k, w)).sum();
    ensure(tail == BigUint::from(good), || {
        format!("F5 binomial identity failed at k={k}")
    })?;
    Ok(GoodCount {
        level: k,
        good,
        total,
        max_weight,
        binomial_tail: tail.to_string(),
    })
}

fn python_summary_counts(text: &str) -> Check<Vec<(u32, u64, u64, u32)>> {
    let mut rows = Vec::new();
    for line in text.lines() {
        let cells: Vec<_> = line.split('|').map(str::trim).collect();
        if cells.len() != 7 {
            continue;
        }
        if let Ok(level) = cells[1].parse::<u32>() {
            rows.push((
                level,
                cells[2]
                    .parse()
                    .map_err(|_| "invalid Python summary count")?,
                cells[3]
                    .parse()
                    .map_err(|_| "invalid Python summary denominator")?,
                cells[5]
                    .parse()
                    .map_err(|_| "invalid Python summary weight")?,
            ));
        }
    }
    ensure(rows.len() == 3, || {
        "Python summary must contain the three certified levels".into()
    })?;
    Ok(rows)
}

fn verify(raw: &Path, output_dir: &Path) -> Check<()> {
    let started = Instant::now();
    let (rows, input_sha256) = read_variants(raw)?;
    let mut rng = ShakeRng::new(FUZZ_DOMAIN);
    for _ in 0..500 {
        check_orbit_formula(
            rng.range_u64(0, 1_000_000).into(),
            (rng.range_u64(1, 1_000_000) | 1).into(),
            rng.range_u64(0, 1_000_000).into(),
            rng.range_u64(0, 60) as usize,
        )?;
    }
    let low = BigUint::from(10_u32).pow(50);
    let high = BigUint::from(10_u32).pow(60);
    for _ in 0..20 {
        let a = rng.range_big(&low, &high);
        let mut c = rng.range_big(&low, &high);
        c.set_bit(0, true);
        check_orbit_formula(a, c, rng.range_big(&low, &high), 15)?;
    }
    for (a, c, x, n) in [
        (0_u32, 1_u32, 0_u32, 0),
        (0, 1, 123, 25),
        (2, 3, 0, 59),
        (1, 1, 0, 59),
    ] {
        check_orbit_formula(a.into(), c.into(), x.into(), n)?;
    }
    println!(
        "F1 PASS  500 small + 20 sixty-digit SHAKE cases; 4 explicit zero/even/identity edge cases"
    );

    let mut ncyc = 0;
    let mut subgroup_members = 0;
    for row in &rows {
        if row.c < 0 {
            continue;
        }
        for cy in &row.cycles {
            let members = check_cycle(row.a, row.c as u64, cy)
                .map_err(|e| format!("a={}, c={}, min={}: {e}", row.a, row.c, cy.min))?;
            if row.a == 7 {
                let allowed: Vec<_> = [1_u64, 2, 4]
                    .iter()
                    .map(|g| BigUint::from(row.c as u64) * g % 7_u32)
                    .collect();
                for member in &members {
                    ensure(allowed.contains(&(member % 7_u32)), || {
                        "F4 committed mod-7 confinement failed".into()
                    })?;
                    subgroup_members += 1;
                }
            }
            ncyc += 1;
        }
    }
    println!(
        "F2 PASS  additive/subtractive equations and expansion for {ncyc} positive-c cycles; finite replay validates every stored metric"
    );

    let primes = [2_u64, 3, 5, 7, 11, 13, 101];
    for _ in 0..300 {
        let p = primes[rng.range_u64(0, primes.len() as u64) as usize];
        let a = BigUint::from(p * rng.range_u64(1, 1000));
        let mut c = rng.range_u64(1, 1000);
        if c.is_multiple_of(p) {
            c += 1;
        }
        let c = BigUint::from(c);
        let mut value = BigUint::from(2 * rng.range_u64(1, 1_000_000) + 1);
        t_step(&a, &c, &mut value);
        for _ in 0..200 {
            ensure(!(&value % p).is_zero(), || "F3 repulsion failed".into())?;
            t_step(&a, &c, &mut value);
        }
    }
    println!("F3 PASS  repulsion on 300 systems x 200 ordinary steps");

    for _ in 0..200 {
        let a = BigUint::from(rng.range_u64(3, 10_000) | 1);
        let c = BigUint::from(rng.range_u64(1, 10_000) | 1);
        let mut x = BigUint::from(rng.range_u64(1, 1_000_000) | 1);
        let mut powers = Vec::with_capacity(70);
        let mut power = BigUint::one();
        for _ in 0..70 {
            powers.push(power.clone());
            power = power * 2_u32 % &a;
        }
        for _ in 0..50 {
            x = accelerated(&a, &c, &x)?;
            let remainder = &x % &a;
            ensure(
                powers.iter().any(|p| &remainder * p % &a == &c % &a),
                || "F4 coset confinement failed within legacy 70-exponent witness bound".into(),
            )?;
        }
    }
    println!(
        "F4 PASS  200 systems x 50 accelerated steps; {subgroup_members} complete committed (7,c) cycle members checked"
    );

    for _ in 0..500 {
        let k = rng.range_u64(0, 30) as u32;
        let q = BigUint::from(rng.range_u64(0, 1_000_000_000));
        let s = BigUint::from(rng.range_u64(0, 1_000_000_000));
        ensure(
            uk(k, &((&q << k as usize) + &s))
                == BigUint::from(3_u32).pow(weight(k, &s)) * &q + uk(k, &s),
            || "F5 U-affine identity failed".into(),
        )?;
    }
    let mut descent_checks = 0;
    for _ in 0..300 {
        let k = rng.range_u64(1, 22) as u32;
        let s = BigUint::from(rng.range_u64(0, 1_u64 << k));
        let modulus = BigUint::one() << k as usize;
        if BigUint::from(3_u32).pow(weight(k, &s)) >= modulus {
            continue;
        }
        let q = (BigUint::one() << (2 * k) as usize) + rng.range_u64(0, 1_000_000);
        let n = (&q << k as usize) + s;
        ensure(uk(k, &n) < n, || "F5 finite Terras descent failed".into())?;
        descent_checks += 1;
    }
    println!(
        "F5a PASS  500 affine cases and {descent_checks} qualifying descent cases from 300 attempts"
    );
    let mut counts = Vec::new();
    for (k, expected) in LEVELS {
        let count = count_good(k)?;
        ensure(count.good == expected, || {
            format!("F5 Lean count mismatch for level {k}")
        })?;
        counts.push(count);
    }
    let baseline_path = Path::new(ROOT).join("results/frontier_summary.md");
    let baseline = fs::read_to_string(&baseline_path).map_err(|e| e.to_string())?;
    let expected = python_summary_counts(&baseline)?;
    let actual: Vec<_> = counts
        .iter()
        .map(|c| (c.level, c.good, c.total, c.max_weight))
        .collect();
    ensure(actual == expected, || {
        "direct Rust counts disagree with committed Python summary".into()
    })?;
    println!(
        "F5b PASS  direct BigUint residue counts 219/58651/910596 match Lean, Python, and independent binomial tails"
    );

    let mut markdown = format!(
        "# Frontier verification summary (Rust)\n\nAll F1–F5 exact-arithmetic checks passed. Fuzz stream: `{FUZZ_DOMAIN}` using SHAKE256; these inputs differ from Python's seeded MT stream. The explicit committed cycles and complete residue enumerations are shared and independently checked.\n\n- F1: 500 small + 20 sixty-digit cases, plus 4 explicit edge cases.\n- F2: {ncyc} positive-c cycles; bounded replay checks return, primitive length, H, raw length, minimum, peak, and member prefix. Negative-c rows are excluded from the positive-c theorem.\n- F3: 300 systems × 200 steps.\n- F4: 200 systems × 50 steps; {subgroup_members} complete committed mod-7 cycle members.\n- F5a: 500 affine checks; {descent_checks} qualifying descent checks from 300 attempted inputs.\n- F5b: direct BigUint trajectory enumeration for every residue at each listed level, equal to both the Python summary and independent binomial counts.\n\n| level k | good residues | of 2^k | density | max weight |\n|---:|---:|---:|---:|---:|\n"
    );
    for c in &counts {
        markdown.push_str(&format!(
            "| {} | {} | {} | {:.4}% | {} |\n",
            c.level,
            c.good,
            c.total,
            100.0 * c.good as f64 / c.total as f64,
            c.max_weight
        ));
    }
    markdown.push_str("\nThese are finite cross-checks. The underlying Lean descent theorem covers all n ≥ 8^k in each counted class; these finite results do not prove the Collatz conjecture. Input validation limits are rejection conditions, never evidence of divergence.\n");
    fs::create_dir_all(output_dir).map_err(|e| e.to_string())?;
    fs::write(output_dir.join("frontier_summary_rust.md"), markdown).map_err(|e| e.to_string())?;
    let summary = json!({"schema": 1, "implementation": "Rust", "status": "passed", "input": raw,
        "input_sha256": input_sha256, "fuzz_domain": FUZZ_DOMAIN,
        "fuzz_relation_to_python": "distinct deterministic SHAKE256 stream; Python uses MT",
        "orbit_formula_random_cases": 520, "orbit_formula_edge_cases": 4,
        "positive_cycles_checked": ncyc, "repulsion_systems": 300, "repulsion_steps": 200,
        "coset_systems": 200, "coset_steps": 50, "committed_mod7_members_checked": subgroup_members,
        "affine_cases": 500, "descent_attempts": 300, "descent_checks": descent_checks,
        "counts": counts, "python_count_parity": true, "elapsed_seconds": started.elapsed().as_secs_f64(),
        "validation_limits": {"max_input_bytes": MAX_INPUT_BYTES,"max_cycle_steps": MAX_CYCLE_STEPS,
            "max_orbit_bits": MAX_ORBIT_BITS,"max_total_halvings": MAX_TOTAL_HALVINGS}});
    fs::write(
        output_dir.join("frontier_verification_rust.json"),
        format!(
            "{}\n",
            serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())?
        ),
    )
    .map_err(|e| e.to_string())?;
    println!("== ALL FRONTIER RUST EXACT-ARITHMETIC VERIFICATIONS PASS ==");
    Ok(())
}

fn run() -> Check<()> {
    let mut input = PathBuf::from(ROOT).join("results/raw.jsonl");
    let mut output = PathBuf::from(ROOT).join("results");
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--input" => input = args.next().ok_or("--input requires a JSONL path")?.into(),
            "--output-dir" => output = args.next().ok_or("--output-dir requires a path")?.into(),
            "--help" | "-h" => {
                println!(
                    "verify-frontier [--input RAW.jsonl] [--output-dir DIR]\nExact F1–F5 verification; use cargo run --release --bin verify-frontier"
                );
                return Ok(());
            }
            _ => return Err(format!("unknown argument {arg}")),
        }
    }
    for name in [
        "frontier_summary_rust.md",
        "frontier_verification_rust.json",
    ] {
        ensure(
            !collatz_search::same_existing_file(&input, &output.join(name))
                .map_err(|e| e.to_string())?,
            || format!("output {name} must not overwrite input"),
        )?;
    }
    verify(&input, &output)
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

    #[test]
    fn committed_positive_cycles_replay_with_all_metrics() {
        let (rows, _) = read_variants(&Path::new(ROOT).join("results/raw.jsonl")).unwrap();
        let mut count = 0;
        for row in rows {
            if row.c > 0 {
                for cycle in row.cycles {
                    check_cycle(row.a, row.c as u64, &cycle).unwrap();
                    count += 1;
                }
            }
        }
        assert_eq!(count, 86);
    }

    #[test]
    fn malformed_cycles_stop_at_validated_bounds() {
        let valid = Cycle {
            min: 1,
            k: 1,
            h: 2,
            len: 3,
            max: 4,
            members: vec![1],
        };
        assert!(check_cycle(3, 1, &valid).is_ok());
        let mut wrong = valid.clone();
        wrong.k = 0;
        assert!(check_cycle(3, 1, &wrong).is_err());
        wrong.k = MAX_CYCLE_STEPS + 1;
        assert!(check_cycle(3, 1, &wrong).is_err());
        wrong = valid.clone();
        wrong.k = 2;
        assert!(check_cycle(3, 1, &wrong).is_err());
        wrong = valid.clone();
        wrong.min = 3;
        wrong.members = vec![3];
        assert!(check_cycle(3, 1, &wrong).is_err());
        wrong = valid;
        wrong.h = 99;
        assert!(check_cycle(3, 1, &wrong).is_err());
    }

    #[test]
    fn direct_counts_match_python_and_lean_at_all_levels() {
        let text = fs::read_to_string(Path::new(ROOT).join("results/frontier_summary.md")).unwrap();
        let expected = python_summary_counts(&text).unwrap();
        let actual: Vec<_> = LEVELS
            .iter()
            .map(|(k, value)| {
                let result = count_good(*k).unwrap();
                assert_eq!(result.good, *value);
                (result.level, result.good, result.total, result.max_weight)
            })
            .collect();
        assert_eq!(actual, expected);
    }
}
