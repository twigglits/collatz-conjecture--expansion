# Frontier verification summary (Rust)

All F1–F5 exact-arithmetic checks passed. Fuzz stream: `verify-frontier-rust-v1:20260704` using SHAKE256; these inputs differ from Python's seeded MT stream. The explicit committed cycles and complete residue enumerations are shared and independently checked.

- F1: 500 small + 20 sixty-digit cases, plus 4 explicit edge cases.
- F2: 86 positive-c cycles; bounded replay checks return, primitive length, H, raw length, minimum, peak, and member prefix. Negative-c rows are excluded from the positive-c theorem.
- F3: 300 systems × 200 steps.
- F4: 200 systems × 50 steps; 32 complete committed mod-7 cycle members.
- F5a: 500 affine checks; 234 qualifying descent checks from 300 attempted inputs.
- F5b: direct BigUint trajectory enumeration for every residue at each listed level, equal to both the Python summary and independent binomial counts.

| level k | good residues | of 2^k | density | max weight |
|---:|---:|---:|---:|---:|
| 8 | 219 | 256 | 85.5469% | 5 |
| 16 | 58651 | 65536 | 89.4943% | 10 |
| 20 | 910596 | 1048576 | 86.8412% | 12 |

These are finite cross-checks. The underlying Lean descent theorem covers all n ≥ 8^k in each counted class; these finite results do not prove the Collatz conjecture. Input validation limits are rejection conditions, never evidence of divergence.
