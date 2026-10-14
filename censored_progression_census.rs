//! Exact finite interval census, not a proof of an asymptotic estimate.
//! Every input takes at most 8*k ordinary steps; no later convergence is assumed.
use std::env;

const SCALE: u128 = 1_u128 << 64;

fn ceil_div(n: u128, d: u128) -> u128 {
    n / d + u128::from(n % d != 0)
}

fn main() {
    let k: u32 = env::args().nth(1).expect("binary exponent required").parse().unwrap();
    assert!((1..=20).contains(&k)); // All aggregate cross products fit u128.
    let x_cut = 1_u64 << k;
    let y_cut = 3 * x_cut + 2;
    let horizon = 8 * k;
    let (mut all_lo, mut all_hi, mut prog_lo, mut prog_hi) = (0_u128, 0_u128, 0_u128, 0_u128);
    let (mut corr_lo, mut corr_hi) = (0_u128, 0_u128);
    let (mut steps, mut odd_steps, mut alive, mut prog_count) = (0_u64, 0_u64, 0_u64, 0_u64);
    for n in 1..=y_cut {
        let (mut state, mut t) = (n, 0_u32);
        let (mut w_lo, mut w_hi) = (SCALE, SCALE);
        let (mut a_lo, mut a_hi) = (0_u128, 0_u128);
        while t < horizon && state != 1 {
            a_lo += SCALE - w_hi;
            a_hi += SCALE - w_lo;
            if state % 2 == 1 {
                let numerator = state.checked_mul(3).expect("state overflow");
                let denominator = numerator.checked_add(1).expect("state overflow");
                w_lo = w_lo.checked_mul(u128::from(numerator)).unwrap() / u128::from(denominator);
                w_hi = ceil_div(w_hi.checked_mul(u128::from(numerator)).unwrap(), u128::from(denominator));
                state = denominator;
                odd_steps += 1;
            } else {
                state /= 2;
            }
            assert!(w_lo <= w_hi && w_hi <= SCALE);
            t += 1;
            steps += 1;
        }
        alive += u64::from(state != 1);
        assert!(a_lo <= a_hi && a_hi <= u128::from(horizon) * SCALE);
        all_lo = all_lo.checked_add(a_lo).unwrap();
        all_hi = all_hi.checked_add(a_hi).unwrap();
        if n >= 5 && n % 3 == 2 {
            prog_count += 1;
            prog_lo = prog_lo.checked_add(a_lo).unwrap();
            prog_hi = prog_hi.checked_add(a_hi).unwrap();
            // Exact transport correction: [1+min(horizon,tau(n))-A_horizon(n)]/(2n).
            let cap = u128::from(t + 1) * SCALE;
            let denominator = 2 * u128::from(n);
            corr_lo += (cap - a_hi) / denominator;
            corr_hi += ceil_div(cap - a_lo, denominator);
        }
    }
    assert_eq!(prog_count, x_cut);
    println!(concat!(
        "{{\"binary_exponent\":{},\"X\":{},\"Y\":{},\"ordinary_clock\":{},",
        "\"scale\":\"{}\",\"prefix_sum_lower\":\"{}\",\"prefix_sum_upper\":\"{}\",",
        "\"progression_sum_lower\":\"{}\",\"progression_sum_upper\":\"{}\",",
        "\"correction_sum_lower\":\"{}\",\"correction_sum_upper\":\"{}\",",
        "\"ordinary_steps\":{},\"odd_steps\":{},\"alive_at_cutoff\":{},\"progression_sources\":{}}}"
    ), k, x_cut, y_cut, horizon, SCALE, all_lo, all_hi, prog_lo, prog_hi,
       corr_lo, corr_hi, steps, odd_steps, alive, prog_count);
}
