//! Exact Rust replay of verify_universal.py's V1–V8 checks.

use std::{
    collections::{BTreeSet, HashSet},
    env,
    fmt::Write as _,
    fs::{self, File},
    io::Read,
    path::{Path, PathBuf},
    process,
};

use collatz_search::verify_helpers::{ShakeRng, accelerated, is_power_of_two, odd_part, v2};
use num_bigint::BigUint;
use serde::Deserialize;

const MAX_INPUT_BYTES: u64 = 16 * 1024 * 1024;
const MAX_CENSUS_ENTRIES: usize = 100_000;
const MAX_CATALOG_ENTRIES: usize = 4096;
const MAX_CATALOG_STEPS: u64 = 100_000;
const FUZZ_DOMAIN: &str = "verify-universal-rust-v1:20260703";

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct S1 {
    #[serde(rename = "section")]
    _section: String,
    odd_abelow: u64,
    odd_cbelow: u64,
    pairs: u64,
    n_fixed: u64,
    expected_fixed: u64,
    mersenne_count: u64,
    iff_violations: u64,
    formula_violations: u64,
    pass: bool,
    secs: f64,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct S2 {
    #[serde(rename = "section")]
    _section: String,
    #[serde(rename = "oddACbelow")]
    odd_acbelow: u64,
    odd_xbelow: u64,
    triples: u64,
    n_fixed_found: u64,
    n_matching_law: u64,
    cpu_predicted: u64,
    set_equal: bool,
    pass: bool,
    secs: f64,
    entries: Vec<[u64; 3]>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct S3 {
    #[serde(rename = "section")]
    _section: String,
    odd_abelow: u64,
    fuel: u64,
    periodic: u64,
    escape: u64,
    fuelout: u64,
    all_mersenne_period1: bool,
    pass: bool,
    secs: f64,
    catalog: Vec<[u64; 2]>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct S4 {
    #[serde(rename = "section")]
    _section: String,
    trials: u64,
    violations: u64,
    pass: bool,
    secs: f64,
}

#[derive(Deserialize)]
enum Section {
    S1,
    S2,
    S3,
    S4,
}

#[derive(Deserialize)]
struct SectionTag {
    section: Section,
}

struct Dataset {
    s1: S1,
    s2: S2,
    s3: S3,
    s4: S4,
}

#[derive(Debug, PartialEq, Eq)]
struct CatalogRow {
    a: u64,
    period: u64,
    halvings: u64,
    mersenne: bool,
}

fn require(condition: bool, message: impl Into<String>) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message.into())
    }
}

fn parse_dataset(text: &str) -> Result<Dataset, String> {
    require(
        text.len() as u64 <= MAX_INPUT_BYTES,
        "input exceeds 16 MiB limit",
    )?;
    let (mut s1, mut s2, mut s3, mut s4) = (None, None, None, None);
    let mut count = 0;
    for (index, line) in text.lines().enumerate() {
        count += 1;
        require(count <= 4, "expected exactly four distinct sections S1–S4")?;
        // Parse the tag separately so floating timing fields go directly through
        // serde_json, not Serde's internally tagged buffering (which conflicts
        // with serde_json's arbitrary_precision representation).
        let tag: SectionTag =
            serde_json::from_str(line).map_err(|error| format!("line {}: {error}", index + 1))?;
        match tag.section {
            Section::S1 => require(
                s1.replace(decode_section(line, index)?).is_none(),
                "duplicate S1 section",
            )?,
            Section::S2 => require(
                s2.replace(decode_section(line, index)?).is_none(),
                "duplicate S2 section",
            )?,
            Section::S3 => require(
                s3.replace(decode_section(line, index)?).is_none(),
                "duplicate S3 section",
            )?,
            Section::S4 => require(
                s4.replace(decode_section(line, index)?).is_none(),
                "duplicate S4 section",
            )?,
        }
    }
    let data = Dataset {
        s1: s1.ok_or("missing S1 section")?,
        s2: s2.ok_or("missing S2 section")?,
        s3: s3.ok_or("missing S3 section")?,
        s4: s4.ok_or("missing S4 section")?,
    };
    validate_schema(&data)?;
    Ok(data)
}

fn decode_section<T: serde::de::DeserializeOwned>(line: &str, index: usize) -> Result<T, String> {
    serde_json::from_str(line).map_err(|error| format!("line {}: {error}", index + 1))
}

fn read_dataset(path: &Path) -> Result<Dataset, String> {
    let mut text = String::new();
    File::open(path)
        .map_err(|error| format!("{}: {error}", path.display()))?
        .take(MAX_INPUT_BYTES + 1)
        .read_to_string(&mut text)
        .map_err(|error| format!("{}: {error}", path.display()))?;
    parse_dataset(&text)
}

fn validate_schema(data: &Dataset) -> Result<(), String> {
    let Dataset { s1, s2, s3, s4 } = data;
    for secs in [s1.secs, s2.secs, s3.secs, s4.secs] {
        require(
            secs.is_finite() && secs >= 0.0,
            "invalid GPU timing metadata",
        )?;
    }
    require(
        s1.odd_abelow == 1 << 20 && s1.odd_cbelow == 1 << 20,
        "S1 grid must have odd a,c below 2^20",
    )?;
    require(
        s1.pairs == 1 << 38,
        "S1 pair count does not match grid dimensions",
    )?;
    require(
        s2.odd_acbelow == 512 && s2.odd_xbelow == 1 << 22,
        "S2 grid must have a,c below 512 and x below 2^22",
    )?;
    require(
        s2.triples == 1 << 37,
        "S2 triple count does not match grid dimensions",
    )?;
    require(
        s2.entries.len() <= MAX_CENSUS_ENTRIES,
        "S2 entries exceed the 100000-entry validation limit",
    )?;
    require(
        s2.n_fixed_found == s2.entries.len() as u64
            && s2.n_matching_law == s2.n_fixed_found
            && s2.cpu_predicted == s2.n_fixed_found,
        "S2 counts do not match the supplied census",
    )?;
    require(
        s3.odd_abelow == 1 << 24 && s3.fuel == 4096,
        "S3 grid must have odd a below 2^24 and fuel 4096",
    )?;
    require(
        s3.catalog.len() <= MAX_CATALOG_ENTRIES && s3.periodic == s3.catalog.len() as u64,
        "S3 catalog count is inconsistent or exceeds the 4096-entry limit",
    )?;
    require(
        u128::from(s3.periodic) + u128::from(s3.escape) + u128::from(s3.fuelout) == 1 << 23,
        "S3 status counts do not cover its grid",
    )?;
    let mut seen = HashSet::new();
    let mut total_steps = 0_u64;
    for &[a, period] in &s3.catalog {
        require(a > 0 && a < 1 << 24 && a % 2 == 1, "invalid S3 multiplier")?;
        require(
            period > 0 && period <= s3.fuel,
            "S3 period must lie in 1..=4096",
        )?;
        require(seen.insert(a), format!("duplicate S3 multiplier {a}"))?;
        total_steps += period;
    }
    require(
        total_steps <= MAX_CATALOG_STEPS,
        "S3 catalog exceeds 100000 total exact replay steps",
    )?;
    require(s4.trials == 1 << 33, "S4 trial count must equal 2^33")
}

fn verify_flags_and_census(data: &Dataset) -> Result<usize, String> {
    let Dataset { s1, s2, s4, .. } = data;
    require(
        s1.pass && s1.iff_violations == 0 && s1.formula_violations == 0,
        "V1: S1 GPU flags report a violation",
    )?;
    let mersennes = (1_u64..1 << 20)
        .step_by(2)
        .filter(|a| (a + 1).is_power_of_two())
        .count() as u64;
    require(
        mersennes == 20
            && s1.mersenne_count == mersennes
            && s1.n_fixed == mersennes * (1 << 19)
            && s1.expected_fixed == s1.n_fixed,
        "V1: S1 Mersenne/fixed-point expectation mismatch",
    )?;
    require(
        s4.pass && s4.violations == 0,
        "V1: S4 GPU flags report a violation",
    )?;
    require(
        s2.pass && s2.set_equal,
        "V2: S2 GPU flags report a census mismatch",
    )?;

    let mut gpu = BTreeSet::new();
    for &[a, c, x] in &s2.entries {
        require(
            a > 0
                && a < 512
                && a % 2 == 1
                && c > 0
                && c < 512
                && c % 2 == 1
                && x > 0
                && x < 1 << 22
                && x % 2 == 1,
            format!("V2: out-of-grid census entry ({a}, {c}, {x})"),
        )?;
        require(
            gpu.insert((a, c, x)),
            format!("V2: duplicate census entry ({a}, {c}, {x})"),
        )?;
    }
    let mut predicted = BTreeSet::new();
    for a in (1_u64..512).step_by(2) {
        for c in (1_u64..512).step_by(2) {
            for d in (1..=c).step_by(2) {
                if c % d == 0 && (a + d).is_power_of_two() && c / d < 1 << 22 {
                    predicted.insert((a, c, c / d));
                }
            }
        }
    }
    require(
        gpu == predicted,
        format!(
            "V2: census differs from divisor law (GPU={}, predicted={})",
            gpu.len(),
            predicted.len()
        ),
    )?;
    for &(a, c, x) in &gpu {
        require(
            accelerated(&BigUint::from(a), &BigUint::from(c), &BigUint::from(x))?
                == BigUint::from(x),
            format!("V2: ({a}, {c}, {x}) is not fixed"),
        )?;
    }
    Ok(gpu.len())
}

fn verify_catalog_entry(a: u64, period: u64) -> Result<CatalogRow, String> {
    require(a > 0 && a < 1 << 24 && a % 2 == 1, "V3: invalid multiplier")?;
    require((1..=4096).contains(&period), "V3: invalid period")?;
    let multiplier = BigUint::from(a);
    let one = BigUint::from(1_u8);
    let mut x = one.clone();
    let mut weight = BigUint::default();
    let mut two_power = one.clone();
    let mut total_halvings = 0_u64;
    for elapsed in 1..=period {
        let value = &multiplier * &x + &one;
        let halvings = v2(&value)?;
        weight = &multiplier * weight + &two_power;
        two_power <<= halvings;
        total_halvings += halvings;
        x = value >> halvings;
        require(
            (x == one) == (elapsed == period),
            format!(
                "V3: ({a}, {period}) does not first return at the claimed period; step {elapsed}"
            ),
        )?;
    }
    require(
        two_power == multiplier.pow(period as u32) + weight,
        format!("V3: cycle equation fails for ({a}, {period})"),
    )?;
    let mersenne = (a + 1).is_power_of_two();
    if period == 1 {
        require(
            mersenne,
            format!("V3: period-one multiplier {a} is not Mersenne"),
        )?;
    }
    if period == 2 {
        let m = odd_part(&(&multiplier + &one))?;
        require(
            m > one
                && accelerated(&multiplier, &one, &one)? == m
                && accelerated(&multiplier, &one, &m)? == one
                && is_power_of_two(&(&multiplier * &m + &one)),
            format!("V3: two-cycle arithmetic criterion fails for {a}"),
        )?;
    }
    Ok(CatalogRow {
        a,
        period,
        halvings: total_halvings,
        mersenne,
    })
}

fn verify_catalog(data: &Dataset) -> Result<Vec<CatalogRow>, String> {
    require(
        data.s3.pass && data.s3.all_mersenne_period1,
        "V3: S3 GPU flags report a violation",
    )?;
    let mut rows = Vec::with_capacity(data.s3.catalog.len());
    for &[a, period] in &data.s3.catalog {
        rows.push(verify_catalog_entry(a, period)?);
    }
    let period_one: BTreeSet<_> = rows
        .iter()
        .filter(|row| row.period == 1)
        .map(|row| row.a)
        .collect();
    let expected: BTreeSet<_> = (1..=24).map(|k| (1_u64 << k) - 1).collect();
    require(
        period_one == expected,
        "V3: period-one catalog is not exactly 2^k−1, k=1..24",
    )?;
    rows.sort_by_key(|row| row.a);
    Ok(rows)
}

fn odd(mut value: BigUint) -> BigUint {
    value.set_bit(0, true);
    value
}

fn verify_large_identities(catalog: &[CatalogRow]) -> Result<(), String> {
    let mut rng = ShakeRng::new(FUZZ_DOMAIN);
    let zero = BigUint::default();
    let one = BigUint::from(1_u8);
    let ten = BigUint::from(10_u8);
    let (p60, p80, p100, p101, p150, p200, p350) = (
        ten.pow(60),
        ten.pow(80),
        ten.pow(100),
        ten.pow(101),
        ten.pow(150),
        ten.pow(200),
        ten.pow(350),
    );

    for trial in 0..300 {
        let c = odd(rng.range_big(&p200, &p350));
        let k = rng.range_u64(1, 500);
        let a = (&one << k) - &one;
        require(
            accelerated(&a, &c, &c)? == c,
            format!("V4 trial {trial}: universal fixed-point failure"),
        )?;
        let a2 = odd(rng.range_big(&p60, &p100));
        let m = odd_part(&(&a2 + &one))?;
        let image = accelerated(&a2, &c, &c)?;
        require(
            image == &m * &c,
            format!("V4 trial {trial}: master formula failure"),
        )?;
        if !is_power_of_two(&(&a2 + &one)) {
            require(image != c, format!("V4 trial {trial}: rigidity failure"))?;
        }
    }
    println!(
        "V4 PASS  master formula and Mersenne rigidity; 300 SHAKE trials with c in [10^200,10^350)"
    );

    for trial in 0..300 {
        let a = rng.range_big(&zero, &p80);
        let u = rng.range_big(&zero, &p80);
        let d = odd(rng.range_big(&zero, &p80));
        let e = odd(rng.range_big(&zero, &p80));
        require(
            accelerated(&a, &(&d * &e), &(&d * &u))? == &d * accelerated(&a, &e, &u)?,
            format!("V5 trial {trial}: scaling identity failure"),
        )?;
    }
    println!("V5 PASS  F(a,d*e,d*u)=d*F(a,e,u); 300 SHAKE trials at 80-digit scale");

    for row in catalog {
        let a = BigUint::from(row.a);
        for trial in 0..5 {
            let c = odd(rng.range_big(&p100, &p101));
            let mut x = c.clone();
            for elapsed in 1..=row.period {
                x = accelerated(&a, &c, &x)?;
                require(
                    (x == c) == (elapsed == row.period),
                    format!(
                        "V6 multiplier {}, trial {trial}: transported first return mismatch",
                        row.a
                    ),
                )?;
            }
        }
    }
    println!(
        "V6 PASS  all {} catalog families transported to c in [10^100,10^101); exact first return",
        catalog.len()
    );

    let a = BigUint::from(181_u16);
    for trial in 0..100 {
        let c = odd(rng.range_big(&p100, &p150));
        let x = &c * 27_u8;
        let y = &c * 611_u16;
        require(
            accelerated(&a, &c, &x)? == y && accelerated(&a, &c, &y)? == x,
            format!("V7 trial {trial}: 181-family transport failure"),
        )?;
    }
    println!("V7 PASS 181x+c cycle {{27c,611c}}; 100 SHAKE trials with c in [10^100,10^150)");
    Ok(())
}

fn divisors(n: u64) -> Vec<u64> {
    let mut result = Vec::new();
    let mut d = 1;
    while d <= n / d {
        if n.is_multiple_of(d) {
            result.push(d);
            if d != n / d {
                result.push(n / d);
            }
        }
        d += 1;
    }
    result.sort_unstable();
    result
}

fn verify_composite_law() -> Result<(), String> {
    let c = 3_u64.pow(5) * 5_u64.pow(2) * 7 * 11 * 13;
    let c_big = BigUint::from(c);
    let divisors = divisors(c);
    for a in (3_u64..202).step_by(2) {
        let a_big = BigUint::from(a);
        let predicted: BTreeSet<_> = divisors
            .iter()
            .filter(|&&d| (a + d).is_power_of_two())
            .map(|d| c / d)
            .collect();
        for &x in &predicted {
            require(
                accelerated(&a_big, &c_big, &BigUint::from(x))? == BigUint::from(x),
                format!("V8: predicted fixed point ({a}, {c}, {x}) fails"),
            )?;
        }
        if a == 3 {
            let mut found = BTreeSet::new();
            for x in (1_u64..=2_000_001).step_by(2) {
                let value = BigUint::from(x);
                if accelerated(&a_big, &c_big, &value)? == value {
                    found.insert(x);
                }
            }
            let restricted: BTreeSet<_> =
                predicted.into_iter().filter(|&x| x <= 2_000_001).collect();
            require(
                found == restricted,
                "V8: brute scan differs from the divisor prediction",
            )?;
        }
    }
    println!(
        "V8 PASS  one-step law at c={c}, odd a=3..201; a=3 brute scan through 2,000,001 complete"
    );
    Ok(())
}

fn summary(data: &Dataset, rows: &[CatalogRow]) -> String {
    let Dataset { s1, s2, s3, s4 } = data;
    let mut out = String::from("# Universal-cycle verification summary (Rust)\n\n");
    writeln!(out, "- S1 rigidity grid: {} (a,c) pairs, odd a,c < 2^20 — formula violations {}, iff violations {}, fixed points {} = 20 Mersenne a x 2^19 c  [{:.2}s GPU]", s1.pairs, s1.formula_violations, s1.iff_violations, s1.n_fixed, s1.secs).unwrap();
    writeln!(out, "- S2 fixed-point census: {} triples (a,c<512, x<2^22) — {} fixed points, all matching the one-step law, set-equal to exact divisor enumeration  [{:.2}s GPU]", s2.triples, s2.n_fixed_found, s2.secs).unwrap();
    writeln!(
        out,
        "- S3 catalog: odd a < 2^24, fuel 4096 — periodic {}, escape {}, fuelout {}  [{:.2}s GPU]",
        s3.periodic, s3.escape, s3.fuelout, s3.secs
    )
    .unwrap();
    writeln!(
        out,
        "- S4 scaling fuzz: {} trials, {} violations  [{:.2}s GPU]\n",
        s4.trials, s4.violations, s4.secs
    )
    .unwrap();
    out.push_str("V1–V8 passed using exact arbitrary-precision BigUint arithmetic. The original GPU grids were not rerun: GPU flags were checked, census entries and catalog trajectories independently replayed, and the fixed-point census independently reconstructed.\n\n");
    writeln!(out, "The large-integer trials use deterministic SHAKE256 rejection sampling with domain `{FUZZ_DOMAIN}`. They retain the Python ranges and trial counts, but use a different sample stream from Python's Mersenne Twister. V6 additionally checks the first return at every transported period.\n").unwrap();
    out.push_str("Window escapes remain unresolved for eventual periodicity. Zero fuel-outs does not make this catalog complete: an escaped orbit might return later.\n\n");
    out.push_str("## Universal cycle families found (1 periodic under F_{a,1}, a < 2^24)\n\n| a | period k | H (halvings) | a+1 power of 2? |\n|---:|---:|---:|:---:|\n");
    for row in rows {
        writeln!(
            out,
            "| {} | {} | {} | {} |",
            row.a,
            row.period,
            row.halvings,
            if row.mersenne { "yes" } else { "NO" }
        )
        .unwrap();
    }
    out
}

fn run() -> Result<(), String> {
    let mut input = PathBuf::from("results/universal.jsonl");
    let mut output = PathBuf::from("results/universal_summary_rust.md");
    let mut args = env::args_os().skip(1);
    while let Some(arg) = args.next() {
        match arg.to_str() {
            Some("--input") => input = PathBuf::from(args.next().ok_or("--input needs a path")?),
            Some("--output") => output = PathBuf::from(args.next().ok_or("--output needs a path")?),
            Some("--help" | "-h") => {
                println!(
                    "Usage: verify-universal [--input results/universal.jsonl] [--output results/universal_summary_rust.md]\n\nReplays V1–V8 with exact BigUint arithmetic. SHAKE256 fuzz samples differ from Python MT. Input limit: 16 MiB; four sections; 100000 census entries; 4096 catalog entries and 100000 total replay steps."
                );
                return Ok(());
            }
            _ => return Err(format!("unknown argument {}", arg.to_string_lossy())),
        }
    }
    require(
        !collatz_search::same_existing_file(&input, &output).map_err(|error| error.to_string())?,
        "output must not overwrite input",
    )?;
    let data = read_dataset(&input)?;
    let census_count = verify_flags_and_census(&data)?;
    println!("V1 PASS  S1/S4 flags, dimensions, counts and Mersenne expectations");
    println!(
        "V2 PASS  S2 census: {census_count} fixed points; exact divisor-law set equality and direct replay"
    );
    let catalog = verify_catalog(&data)?;
    println!(
        "V3 PASS  S3 catalog: {} families; exact first returns, cycle equations and 24 Mersennes",
        catalog.len()
    );
    verify_large_identities(&catalog)?;
    verify_composite_law()?;
    if let Some(parent) = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    }
    fs::write(&output, summary(&data, &catalog))
        .map_err(|error| format!("{}: {error}", output.display()))?;
    println!(
        "wrote {}\n== ALL EXACT-ARITHMETIC VERIFICATIONS PASS ==",
        output.display()
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("verify-universal: {error}");
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIXTURE: &str = include_str!("../../results/universal.jsonl");

    #[test]
    fn committed_gpu_census_and_catalog_replay_exactly() {
        let data = parse_dataset(FIXTURE).unwrap();
        assert_eq!(verify_flags_and_census(&data).unwrap(), 5477);
        let catalog = verify_catalog(&data).unwrap();
        assert_eq!(catalog.len(), 25);
        assert!(catalog.contains(&CatalogRow {
            a: 5,
            period: 2,
            halvings: 5,
            mersenne: false
        }));
        assert_eq!(catalog.iter().filter(|row| row.period == 1).count(), 24);
    }

    #[test]
    fn duplicate_sections_and_wrong_dimensions_are_rejected() {
        let first = FIXTURE.lines().next().unwrap();
        assert!(parse_dataset(&format!("{first}\n{first}\n")).is_err());
        let changed = FIXTURE.replacen("\"oddAbelow\":1048576", "\"oddAbelow\":1048577", 1);
        assert!(parse_dataset(&changed).is_err());
    }

    #[test]
    fn invalid_and_nonminimal_periods_are_rejected() {
        assert!(verify_catalog_entry(5, 0).is_err());
        assert!(verify_catalog_entry(5, u64::MAX).is_err());
        assert!(verify_catalog_entry(5, 1).is_err());
        assert!(verify_catalog_entry(5, 4).is_err());
        assert!(verify_catalog_entry(5, 2).is_ok());
    }

    #[test]
    fn duplicate_census_entries_do_not_hide_in_set_conversion() {
        let mut data = parse_dataset(FIXTURE).unwrap();
        data.s2.entries[1] = data.s2.entries[0];
        assert!(verify_flags_and_census(&data).is_err());
    }

    #[test]
    fn composite_divisor_enumeration_is_complete() {
        let values = divisors(6_081_075);
        assert_eq!(values.len(), 6 * 3 * 2 * 2 * 2);
        assert_eq!(values[0], 1);
        assert_eq!(*values.last().unwrap(), 6_081_075);
        assert!(values.iter().all(|d| 6_081_075 % d == 0));
        assert!(values.windows(2).all(|pair| pair[0] < pair[1]));
    }
}
