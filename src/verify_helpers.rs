//! Exact arithmetic shared by the independent CUDA-result verifiers.

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};
use sha3::{
    Shake256,
    digest::{ExtendableOutput, Update, XofReader},
};

/// The exponent of two dividing a positive integer; zero is not accepted.
pub fn v2(n: &BigUint) -> Result<u64, String> {
    n.trailing_zeros()
        .ok_or_else(|| "the 2-adic valuation of zero is undefined".to_owned())
}

pub fn odd_part(n: &BigUint) -> Result<BigUint, String> {
    Ok(n >> v2(n)?)
}

pub fn accelerated(a: &BigUint, c: &BigUint, x: &BigUint) -> Result<BigUint, String> {
    odd_part(&(a * x + c))
}

pub fn is_power_of_two(n: &BigUint) -> bool {
    n.trailing_zeros()
        .is_some_and(|zeros| zeros + 1 == n.bits())
}

/// Reproducible SHAKE256 samples, independent of Python's Mersenne Twister.
///
/// Each draw hashes the domain and a little-endian counter. Rejection sampling
/// avoids modulo bias. Bounds are programmer-supplied, valid half-open ranges;
/// callers must validate untrusted bounds before using this helper.
pub struct ShakeRng {
    domain: Vec<u8>,
    counter: u64,
}

impl ShakeRng {
    pub fn new(domain: &str) -> Self {
        Self {
            domain: domain.as_bytes().to_vec(),
            counter: 0,
        }
    }

    fn below(&mut self, high: &BigUint) -> BigUint {
        assert!(!high.is_zero(), "sampling upper bound must be positive");
        let bits = (high - 1_u8).bits();
        if bits == 0 {
            return BigUint::default();
        }
        let byte_count = usize::try_from(bits.div_ceil(8)).expect("sample fits address space");
        loop {
            let mut hasher = Shake256::default();
            hasher.update(&self.domain);
            hasher.update(&[0]);
            hasher.update(&self.counter.to_le_bytes());
            self.counter = self
                .counter
                .checked_add(1)
                .expect("SHAKE counter exhausted");
            let mut reader = hasher.finalize_xof();
            let mut bytes = vec![0_u8; byte_count];
            reader.read(&mut bytes);
            if !bits.is_multiple_of(8) {
                bytes[0] &= (1_u8 << (bits % 8)) - 1;
            }
            let value = BigUint::from_bytes_be(&bytes);
            if &value < high {
                return value;
            }
        }
    }

    pub fn range_big(&mut self, low: &BigUint, high: &BigUint) -> BigUint {
        assert!(low < high, "sampling range must be nonempty");
        low + self.below(&(high - low))
    }

    pub fn range_u64(&mut self, low: u64, high: u64) -> u64 {
        assert!(low < high, "sampling range must be nonempty");
        self.range_big(&BigUint::from(low), &BigUint::from(high))
            .to_u64()
            .expect("sample remains within u64 bounds")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valuation_and_odd_part_are_exact_above_machine_word_size() {
        let odd = BigUint::from(611_u16);
        let value = &odd << 8192_usize;
        assert_eq!(v2(&value).unwrap(), 8192);
        assert_eq!(odd_part(&value).unwrap(), odd);
        assert!(v2(&BigUint::default()).is_err());
        assert!(odd_part(&BigUint::default()).is_err());
        assert!(is_power_of_two(&(BigUint::from(1_u8) << 10000_usize)));
        assert!(!is_power_of_two(&BigUint::default()));
    }

    #[test]
    fn fixed_domain_repeats_samples_and_ranges_are_half_open() {
        let mut first = ShakeRng::new("verifier-test-v1");
        let mut second = ShakeRng::new("verifier-test-v1");
        let low = BigUint::from(10_u8).pow(200);
        let high = BigUint::from(10_u8).pow(350);
        for _ in 0..100 {
            let sample = first.range_big(&low, &high);
            assert_eq!(sample, second.range_big(&low, &high));
            assert!(low <= sample && sample < high);
        }
        for _ in 0..100 {
            let sample = first.range_u64(17, 513);
            assert!((17..513).contains(&sample));
        }
        assert_eq!(first.range_u64(42, 43), 42);
    }
}
