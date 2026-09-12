// Unverified diagnostic arithmetic for two k=17, H=27 mutations.
fn numerator(word: &[u32]) -> u128 {
    let mut w = 0_u128;
    let mut power_two = 1_u128;
    for &h in word {
        w = w.checked_mul(3).unwrap().checked_add(power_two).unwrap();
        power_two = power_two.checked_shl(h).unwrap();
    }
    w
}
fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { (a, b) = (b, a % b); }
    a
}
fn main() {
    let word: Vec<u32> = (0..17).map(|i| ((i + 1) * 27 / 17 - i * 27 / 17) as u32).collect();
    let d = 2_u128.pow(27) - 3_u128.pow(17);
    println!("original={word:?}; D={d}");
    for (family, j) in [("22->13", 15), ("121->112", 1)] {
        let mut mutated: Vec<u32> = (0..17).map(|i| word[(j+i)%17]).collect();
        let original_w = numerator(&mutated);
        mutated[0] -= 1;
        mutated[1] += 1;
        let w = numerator(&mutated);
        assert_eq!(original_w - w, 2 * 3_u128.pow(15));
        assert_eq!(gcd(d, w), 5);
        println!("{family}: transfer_index={j}; rotated_mutation={mutated:?}; W={w}; gcd={}; reduced_denominator={}", gcd(d,w), d/gcd(d,w));
    }
}
