//! Unverified exact diagnostics for adjacent defects of mechanical halving words.
//! No floating point enters word generation, divisibility, or gcd calculations.
use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    env,
    fs::{self, File, OpenOptions},
    io::{BufWriter, Write},
    path::PathBuf,
    time::{Duration, Instant},
};

type Result<T> = std::result::Result<T, String>;

#[derive(Debug)]
struct Options {
    min_k: usize,
    max_k: usize,
    stride: usize,
    seconds: u64,
    output_dir: PathBuf,
}

fn options() -> Result<Options> {
    let mut result = Options {
        min_k: 3,
        max_k: 1_000,
        stride: 1,
        seconds: 120,
        output_dir: PathBuf::from("results/cycle-defects/default"),
    };
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg == "--help" || arg == "-h" {
            println!(
                "cycle-defects [--min-k 3] [--max-k 1000] [--stride 1] \
                 [--seconds 120] [--output-dir results/cycle-defects/default]\n\
                 Exact but unverified diagnostics; output files must not already exist.\n\
                 The time limit stops between arithmetic operations and may leave a partial row."
            );
            std::process::exit(0);
        }
        let value = args
            .next()
            .ok_or_else(|| format!("missing value for {arg}"))?;
        match arg.as_str() {
            "--min-k" => result.min_k = value.parse().map_err(|_| "invalid --min-k")?,
            "--max-k" => result.max_k = value.parse().map_err(|_| "invalid --max-k")?,
            "--stride" => result.stride = value.parse().map_err(|_| "invalid --stride")?,
            "--seconds" => result.seconds = value.parse().map_err(|_| "invalid --seconds")?,
            "--output-dir" => result.output_dir = value.into(),
            _ => return Err(format!("unknown argument {arg}")),
        }
    }
    if !(3..=100_000).contains(&result.min_k)
        || result.max_k < result.min_k
        || result.max_k > 100_000
        || result.stride == 0
        || result.stride > 100_000
        || !(1..=86_400).contains(&result.seconds)
    {
        return Err("require 3<=min-k<=max-k<=100000, 1<=stride<=100000, 1<=seconds<=86400".into());
    }
    Ok(result)
}

fn gcd_small(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Binary gcd. The caller's first argument is positive and odd.
fn gcd_odd(modulus: &BigUint, value: &BigUint) -> BigUint {
    if value.is_zero() {
        return modulus.clone();
    }
    let mut a = modulus.clone();
    let mut b = value.clone();
    b >>= b.trailing_zeros().expect("nonzero value");
    loop {
        match a.cmp(&b) {
            std::cmp::Ordering::Equal => return a,
            std::cmp::Ordering::Greater => {
                a -= &b;
                a >>= a.trailing_zeros().expect("positive difference");
            }
            std::cmp::Ordering::Less => {
                b -= &a;
                b >>= b.trailing_zeros().expect("positive difference");
            }
        }
    }
}

fn mechanical(k: usize, h: usize) -> Vec<u8> {
    (0..k)
        .map(|i| {
            let left = (i as u128 * h as u128) / k as u128;
            let right = ((i + 1) as u128 * h as u128) / k as u128;
            u8::try_from(right - left).expect("mechanical symbols fit u8")
        })
        .collect()
}

fn numerator(word: &[u8]) -> BigUint {
    let mut result = BigUint::zero();
    let mut power_two = BigUint::one();
    for &h in word {
        result *= 3_u32;
        result += &power_two;
        power_two <<= h as usize;
    }
    result
}

/// Update the rotated numerator modulo an odd denominator without division.
fn rotate_residue(value: &mut BigUint, h: u8, denominator: &BigUint) {
    *value *= 3_u32;
    while &*value >= denominator {
        *value -= denominator;
    }
    for _ in 0..h {
        if value.bit(0) {
            *value += denominator;
        }
        *value >>= 1_usize;
    }
}

fn modular_difference(a: &BigUint, b: &BigUint, denominator: &BigUint) -> BigUint {
    if a >= b { a - b } else { (a + denominator) - b }
}

#[derive(Clone, Debug, Default, Serialize)]
struct Family {
    cyclic_positions_checked: u64,
    gcd_evaluations: u64,
    gcd_histogram: BTreeMap<String, u64>,
    largest_gcd: String,
    minimum_reduced_denominator_bits: Option<u64>,
    minimum_reduced_denominator_sha256: Option<String>,
    integer_candidates: Vec<IntegerCandidate>,
}

#[derive(Clone, Debug, Serialize)]
struct IntegerCandidate {
    /// Start of the displayed pattern; further starts differ by rotation_period.
    pattern_start: usize,
    transfer_start: usize,
    rotation_period: usize,
    equivalent_positions: usize,
}

impl Family {
    fn record(&mut self, divisor: &BigUint, denominator: &BigUint, candidate: IntegerCandidate) {
        self.cyclic_positions_checked += candidate.equivalent_positions as u64;
        self.gcd_evaluations += 1;
        *self.gcd_histogram.entry(divisor.to_string()).or_default() +=
            candidate.equivalent_positions as u64;
        let is_larger = self.largest_gcd.is_empty()
            || divisor > &self.largest_gcd.parse::<BigUint>().expect("stored integer");
        if is_larger {
            self.largest_gcd = divisor.to_string();
            let reduced = denominator / divisor;
            self.minimum_reduced_denominator_bits = Some(reduced.bits());
            self.minimum_reduced_denominator_sha256 =
                Some(format!("{:x}", Sha256::digest(reduced.to_bytes_be())));
        }
        if divisor == denominator {
            self.integer_candidates.push(candidate);
        }
    }
}

#[derive(Debug, Serialize)]
struct Period {
    k: usize,
    h: usize,
    denominator_bits: u64,
    mechanical_word_period: usize,
    mechanical_word_repetitions: usize,
    base_reduced_denominator_gcd: String,
    complete: bool,
    distinct_rotations_scanned: usize,
    cyclic_rotations_covered: usize,
    transfer_22_to_13: Family,
    transfer_121_to_112: Family,
}

fn scan_period(k: usize, power_three: &BigUint, deadline: Instant) -> Period {
    // 3^k is not a power of two, so bitlength is exactly ceil(k log_2 3).
    let h = usize::try_from(power_three.bits()).expect("bounded bit count");
    let denominator = (BigUint::one() << h) - power_three;
    let repetitions = gcd_small(k, h);
    let period = k / repetitions;
    let period_h = h / repetitions;
    let word = mechanical(period, period_h);
    let primitive_three = if period == k {
        power_three.clone()
    } else {
        BigUint::from(3_u32).pow(period as u32)
    };
    let primitive_denominator = (BigUint::one() << period_h) - primitive_three;
    let scale = &denominator / &primitive_denominator;
    // Exact composition of a repeated affine map scales both W and D equally.
    let primitive_residue = numerator(&word) % &primitive_denominator;
    let mut residue = &primitive_residue * &scale;
    let base_gcd = gcd_odd(&primitive_denominator, &primitive_residue) * &scale;
    let delta = ((power_three / 9_u32) * 2_u32) % &denominator;
    let mut result = Period {
        k,
        h,
        denominator_bits: denominator.bits(),
        mechanical_word_period: period,
        mechanical_word_repetitions: repetitions,
        base_reduced_denominator_gcd: base_gcd.to_string(),
        complete: true,
        distinct_rotations_scanned: 0,
        cyclic_rotations_covered: 0,
        transfer_22_to_13: Family::default(),
        transfer_121_to_112: Family::default(),
    };
    for j in 0..period {
        if Instant::now() >= deadline {
            result.complete = false;
            break;
        }
        if word[j] == 2 {
            let next = word[(j + 1) % period];
            let previous = word[(j + period - 1) % period];
            let kind = if next == 2 {
                Some(false)
            } else if previous == 1 && next == 1 {
                Some(true)
            } else {
                None
            };
            if let Some(is_121) = kind {
                let mutated = modular_difference(&residue, &delta, &denominator);
                let divisor = gcd_odd(&denominator, &mutated);
                let candidate = IntegerCandidate {
                    pattern_start: if is_121 { (j + k - 1) % k } else { j },
                    transfer_start: j,
                    rotation_period: period,
                    equivalent_positions: repetitions,
                };
                if is_121 {
                    result
                        .transfer_121_to_112
                        .record(&divisor, &denominator, candidate);
                } else {
                    result
                        .transfer_22_to_13
                        .record(&divisor, &denominator, candidate);
                }
            }
        }
        rotate_residue(&mut residue, word[j], &denominator);
        result.distinct_rotations_scanned += 1;
        result.cyclic_rotations_covered += repetitions;
    }
    result
}

fn new_file(path: &std::path::Path) -> Result<BufWriter<File>> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map(BufWriter::new)
        .map_err(|error| format!("{}: {error}", path.display()))
}

fn run(opts: Options) -> Result<()> {
    fs::create_dir_all(&opts.output_dir).map_err(|e| e.to_string())?;
    let mut rows = new_file(&opts.output_dir.join("periods.jsonl"))?;
    let mut summary_file = new_file(&opts.output_dir.join("summary.json"))?;
    let started = Instant::now();
    let deadline = started + Duration::from_secs(opts.seconds);
    let mut power_three = BigUint::from(3_u32).pow(opts.min_k as u32);
    let multiplier = BigUint::from(3_u32).pow(opts.stride as u32);
    let mut completed_periods = 0_u64;
    let mut rotations_covered = 0_u64;
    let mut count_22 = 0_u64;
    let mut count_121 = 0_u64;
    let mut gcd_evaluations = 0_u64;
    let mut integer_candidates = 0_u64;
    let mut last_k = None;
    let mut next_k = Some(opts.min_k);
    let mut complete = true;
    let mut row_hash = Sha256::new();
    for k in (opts.min_k..=opts.max_k).step_by(opts.stride) {
        if Instant::now() >= deadline {
            complete = false;
            next_k = Some(k);
            break;
        }
        let row = scan_period(k, &power_three, deadline);
        let mut encoded = serde_json::to_vec(&row).map_err(|e| e.to_string())?;
        encoded.push(b'\n');
        rows.write_all(&encoded).map_err(|e| e.to_string())?;
        row_hash.update(&encoded);
        last_k = Some(k);
        rotations_covered += row.cyclic_rotations_covered as u64;
        for family in [&row.transfer_22_to_13, &row.transfer_121_to_112] {
            gcd_evaluations += family.gcd_evaluations;
            integer_candidates += family
                .integer_candidates
                .iter()
                .map(|c| c.equivalent_positions as u64)
                .sum::<u64>();
        }
        count_22 += row.transfer_22_to_13.cyclic_positions_checked;
        count_121 += row.transfer_121_to_112.cyclic_positions_checked;
        if !row.complete {
            complete = false;
            next_k = Some(k);
            break;
        }
        completed_periods += 1;
        next_k = k.checked_add(opts.stride).filter(|&n| n <= opts.max_k);
        if completed_periods.is_multiple_of(100) || k == opts.min_k {
            eprintln!(
                "k={k}, H={}, gcds={gcd_evaluations}, elapsed={:.3}s",
                row.h,
                started.elapsed().as_secs_f64()
            );
        }
        power_three *= &multiplier;
    }
    rows.flush().map_err(|e| e.to_string())?;
    let summary = serde_json::json!({
        "status": "unverified_diagnostic",
        "mathematical_scope": "No Lean/CUDA certificate; these observations are not certified exclusions.",
        "algorithm": "Exact BigUint powers, floor words, modular rotation, binary gcd; repeated base rotations counted with multiplicity.",
        "parameters": {"min_k": opts.min_k, "max_k": opts.max_k, "stride": opts.stride, "seconds": opts.seconds},
        "complete": complete,
        "stop_reason": if complete {"requested_range_complete"} else {"time_limit_partial_range"},
        "completed_periods": completed_periods,
        "last_attempted_k": last_k,
        "next_or_partial_k": next_k,
        "cyclic_rotations_covered": rotations_covered,
        "mutation_positions": {"22_to_13": count_22, "121_to_112": count_121},
        "gcd_evaluations": gcd_evaluations,
        "integer_candidate_positions": integer_candidates,
        "elapsed_seconds": started.elapsed().as_secs_f64(),
        "source_sha256": format!("{:x}", Sha256::digest(include_bytes!("cycle-defects.rs"))),
        "periods_jsonl_sha256": format!("{:x}", row_hash.finalize()),
        "reduced_denominator_hash_encoding": "SHA256 of unsigned big-endian bytes; exact denominator is (2^H-3^k)/gcd.",
        "output_dir": opts.output_dir,
    });
    serde_json::to_writer_pretty(&mut summary_file, &summary).map_err(|e| e.to_string())?;
    summary_file.write_all(b"\n").map_err(|e| e.to_string())?;
    summary_file.flush().map_err(|e| e.to_string())?;
    println!(
        "{}",
        serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())?
    );
    Ok(())
}

fn main() {
    if let Err(error) = options().and_then(run) {
        eprintln!("cycle-defects: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn euclidean(mut a: BigUint, mut b: BigUint) -> BigUint {
        while !b.is_zero() {
            let remainder = &a % &b;
            a = b;
            b = remainder;
        }
        a
    }

    fn direct_gcd(k: usize, word: &[u8], transfer: usize, denominator: &BigUint) -> BigUint {
        let mut mutated: Vec<u8> = (0..k).map(|i| word[(transfer + i) % k]).collect();
        mutated[0] -= 1;
        mutated[1] += 1;
        euclidean(denominator.clone(), numerator(&mutated))
    }

    #[test]
    fn binary_gcd_agrees_with_independent_euclidean_algorithm() {
        for bits in [1, 7, 64, 127, 257, 1_000] {
            let modulus = (BigUint::one() << bits) + 1_u32;
            for value in [
                BigUint::zero(),
                BigUint::one(),
                &modulus * 9_u32,
                &modulus / 3_u32,
            ] {
                assert_eq!(gcd_odd(&modulus, &value), euclidean(modulus.clone(), value));
            }
        }
    }

    #[test]
    fn exact_bitlength_and_mechanical_period() {
        let mut power_three = BigUint::one();
        for k in 1..=500 {
            power_three *= 3_u32;
            let h = power_three.bits() as usize;
            assert!((BigUint::one() << (h - 1)) < power_three);
            assert!(power_three < (BigUint::one() << h));
            let word = mechanical(k, h);
            assert_eq!(word.iter().map(|&n| n as usize).sum::<usize>(), h);
            let period = k / gcd_small(k, h);
            for i in 0..k {
                assert_eq!(word[i], word[i % period]);
            }
        }
    }

    #[test]
    fn every_mutation_matches_direct_reconstruction_and_euclidean_gcd() {
        for k in 3..=90 {
            let power_three = BigUint::from(3_u32).pow(k as u32);
            let h = power_three.bits() as usize;
            let denominator = (BigUint::one() << h) - &power_three;
            let word = mechanical(k, h);
            let row = scan_period(k, &power_three, Instant::now() + Duration::from_secs(60));
            assert!(row.complete);
            let mut direct_22 = BTreeMap::new();
            let mut direct_121 = BTreeMap::new();
            for j in 0..k {
                if word[j] != 2 {
                    continue;
                }
                let histogram = if word[(j + 1) % k] == 2 {
                    &mut direct_22
                } else if word[(j + k - 1) % k] == 1 && word[(j + 1) % k] == 1 {
                    &mut direct_121
                } else {
                    continue;
                };
                let divisor = direct_gcd(k, &word, j, &denominator);
                *histogram.entry(divisor.to_string()).or_insert(0_u64) += 1;
            }
            assert_eq!(row.transfer_22_to_13.gcd_histogram, direct_22, "22, k={k}");
            assert_eq!(
                row.transfer_121_to_112.gcd_histogram, direct_121,
                "121, k={k}"
            );
            assert_eq!(row.cyclic_rotations_covered, k);
        }
    }

    #[test]
    fn modular_rotation_matches_full_numerators_at_large_bit_width() {
        let k = 701;
        let power_three = BigUint::from(3_u32).pow(k as u32);
        let h = power_three.bits() as usize;
        let denominator = (BigUint::one() << h) - power_three;
        let word = mechanical(k, h);
        let mut residue = numerator(&word) % &denominator;
        let initial = residue.clone();
        for j in 0..k {
            if j.is_multiple_of(97) {
                let rotation: Vec<u8> = (0..k).map(|i| word[(j + i) % k]).collect();
                assert_eq!(residue, numerator(&rotation) % &denominator);
            }
            rotate_residue(&mut residue, word[j], &denominator);
        }
        assert_eq!(residue, initial);
    }
}
