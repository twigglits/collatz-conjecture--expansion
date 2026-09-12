//! Exact positive Collatz trajectories and adversarial parity-prefix residues.
//!
//! Trajectories use ordinary steps, just like `search_counterexample.py`:
//! odd `n` becomes `3*n+1`, and even `n` becomes `n/2`. BigUint prevents
//! fixed-width arithmetic overflow. Exhausting fuel is an unresolved result.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Trace {
    pub status: String,
    pub steps: u64,
    pub peak_bits: u64,
    pub first_descent: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_value: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cycle_value: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cycle_period: Option<u64>,
}

#[inline]
fn step_in_place(n: &mut BigUint) {
    if n.bit(0) {
        *n *= 3_u32;
        *n += 1_u32;
    } else {
        *n >>= 1_usize;
    }
}

/// Trace a positive starting integer using at most `fuel` ordinary steps.
///
/// Brent's cycle detection retains a constant number of arbitrary-precision
/// integers. A detected nontrivial cycle is explicitly marked as requiring a
/// certificate; fuel exhaustion never counts as a counterexample. The initial
/// value is checked before consuming fuel, so `trace(1, 0)` reaches one.
pub fn trace(start: &BigUint, fuel: u64) -> Result<Trace, String> {
    if start.is_zero() {
        return Err("positive start and nonnegative fuel required".to_owned());
    }
    let mut n = start.clone();
    let mut anchor = start.clone();
    // max(bit_length(n_i)) equals bit_length(max(n_i)); storing the full peak
    // integer would perform unnecessary comparisons and copies on every step.
    let mut peak_bits = start.bits();
    let mut first_descent = 0;
    // At the largest possible u64 fuel, Brent's next window can be 2^64.
    // A u128 window avoids overflow without changing the Python algorithm.
    let mut power = 1_u128;
    let mut period = 0_u64;
    if n.is_one() {
        return Ok(Trace {
            status: "reached_one".to_owned(),
            steps: 0,
            peak_bits,
            first_descent,
            last_value: None,
            cycle_value: None,
            cycle_period: None,
        });
    }
    for elapsed in 1..=fuel {
        step_in_place(&mut n);
        peak_bits = peak_bits.max(n.bits());
        if first_descent == 0 && &n < start {
            first_descent = elapsed;
        }
        if n.is_one() {
            return Ok(Trace {
                status: "reached_one".to_owned(),
                steps: elapsed,
                peak_bits,
                first_descent,
                last_value: None,
                cycle_value: None,
                cycle_period: None,
            });
        }
        // period is never greater than elapsed, so it fits within u64 fuel.
        period += 1;
        if n == anchor {
            return Ok(Trace {
                status: "cycle_candidate_requires_certificate".to_owned(),
                steps: elapsed,
                peak_bits,
                first_descent,
                last_value: None,
                cycle_value: Some(n.to_str_radix(10)),
                cycle_period: Some(period),
            });
        }
        if u128::from(period) == power {
            anchor.clone_from(&n);
            period = 0;
            power *= 2;
        }
    }
    Ok(Trace {
        status: "unresolved_fuel".to_owned(),
        steps: fuel,
        peak_bits,
        first_descent,
        last_value: Some(n.to_str_radix(10)),
        cycle_value: None,
        cycle_period: None,
    })
}

/// Construct the Python search's near-critical shortcut parity residue.
///
/// The returned residue modulo `2^length` realizes a parity prefix whose
/// affine slope obeys `3^odd_count >= 2^k` at every prefix length `k`.
/// Lifting the residue by the current modulus flips the next shortcut parity,
/// because the affine numerator's slope is odd. The second return value counts
/// odd steps in the prescribed shortcut prefix, not ordinary Collatz steps.
pub fn critical_residue(length: usize) -> (BigUint, u64) {
    let mut residue = BigUint::zero();
    let mut value = BigUint::zero();
    let mut modulus = BigUint::one();
    let mut slope = BigUint::one();
    let mut ones = 0_u64;
    for level in 0..length {
        // modulus = 2^level, so slope < 2*modulus iff its bit length is
        // at most level+1. This avoids allocating a doubled BigUint each time.
        let want_odd = slope.bits() <= (level + 1) as u64;
        if value.bit(0) != want_odd {
            residue += &modulus;
            value += &slope;
        }
        if want_odd {
            value *= 3_u32;
            value += 1_u32;
            value >>= 1_usize;
            slope *= 3_u32;
            ones += 1;
        } else {
            value >>= 1_usize;
        }
        modulus <<= 1_usize;
    }
    (residue, ones)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};
    use std::fs;
    use std::path::Path;

    #[test]
    fn known_27_trajectory_and_exact_fuel_boundary() {
        let start = BigUint::from(27_u32);
        let reached = trace(&start, 111).unwrap();
        assert_eq!(
            serde_json::to_value(&reached).unwrap(),
            json!({"status": "reached_one", "steps": 111, "peak_bits": 14,
                   "first_descent": 96})
        );
        let unfinished = trace(&start, 110).unwrap();
        assert_eq!(
            serde_json::to_value(&unfinished).unwrap(),
            json!({"status": "unresolved_fuel", "steps": 110, "peak_bits": 14,
                   "first_descent": 96, "last_value": "2"})
        );
    }

    #[test]
    fn zero_and_terminal_starts_do_not_consume_fuel() {
        assert!(trace(&BigUint::zero(), 10).is_err());
        assert_eq!(trace(&BigUint::one(), 0).unwrap().steps, 0);
        assert_eq!(
            trace(&BigUint::one(), u64::MAX).unwrap().status,
            "reached_one"
        );
        assert_eq!(
            serde_json::to_value(trace(&BigUint::from(3_u32), 0).unwrap()).unwrap(),
            json!({"status": "unresolved_fuel", "steps": 0, "peak_bits": 2,
                   "first_descent": 0, "last_value": "3"})
        );
    }

    #[test]
    fn large_power_of_two_uses_exact_arithmetic() {
        let start = BigUint::one() << 4096_usize;
        let result = trace(&start, 4096).unwrap();
        assert_eq!(result.status, "reached_one");
        assert_eq!(result.steps, 4096);
        assert_eq!(result.peak_bits, 4097);
        assert_eq!(result.first_descent, 1);
    }

    #[test]
    fn critical_residue_matches_python_fixtures() {
        let fixtures = [
            (0, "0", 0),
            (1, "1", 1),
            (2, "3", 2),
            (3, "3", 2),
            (4, "11", 3),
            (8, "251", 6),
            (16, "23547", 11),
            (32, "3384695803", 21),
            (64, "12466316350106524667", 41),
            (128, "333565612708162025681028240665193896955", 81),
        ];
        for (length, expected, odd_count) in fixtures {
            let (residue, ones) = critical_residue(length);
            assert_eq!(residue.to_str_radix(10), expected, "length {length}");
            assert_eq!(ones, odd_count, "length {length}");
        }
    }

    #[test]
    fn constructed_prefixes_have_no_descent() {
        for length in [1, 8, 31, 128, 1024] {
            let (residue, expected_ones) = critical_residue(length);
            let start = residue + (BigUint::one() << length);
            let mut value = start.clone();
            let mut ones = 0;
            let mut numerator = BigUint::one();
            let mut denominator = BigUint::one();
            for _ in 0..length {
                if value.bit(0) {
                    ones += 1;
                    value *= 3_u32;
                    value += 1_u32;
                    numerator *= 3_u32;
                }
                value >>= 1_usize;
                denominator <<= 1_usize;
                assert!(value >= start);
                assert!(numerator >= denominator);
            }
            assert_eq!(ones, expected_ones);
        }
    }

    #[test]
    fn large_trajectories_match_existing_lean_certified_manifest() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("results/counterexample_search.json");
        let manifest: Value = serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap();
        assert_eq!(manifest["certificate_status"], "verified");
        let labels = [
            "2^4096-1",
            "11*2^8192-1",
            "critical(8192)+3*2^8192",
            "shake256(4096,17)",
        ];
        for label in labels {
            let expected = manifest["rows"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["label"] == label)
                .unwrap();
            let start =
                BigUint::parse_bytes(expected["start"].as_str().unwrap().as_bytes(), 10).unwrap();
            let actual = trace(&start, expected["steps"].as_u64().unwrap()).unwrap();
            assert_eq!(
                actual.status,
                expected["status"].as_str().unwrap(),
                "{label}"
            );
            assert_eq!(actual.steps, expected["steps"].as_u64().unwrap(), "{label}");
            assert_eq!(
                actual.peak_bits,
                expected["peak_bits"].as_u64().unwrap(),
                "{label}"
            );
            assert_eq!(
                actual.first_descent,
                expected["first_descent"].as_u64().unwrap(),
                "{label}"
            );
            assert!(actual.last_value.is_none());
            assert!(actual.cycle_value.is_none());
            assert!(actual.cycle_period.is_none());
        }
    }
}
