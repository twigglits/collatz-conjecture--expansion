# Frontier verification summary (CollatzFrontier.lean x verify_frontier.py)

| angle | Lean theorem(s) | exact-arithmetic cross-check |
|---|---|---|
| Bohm-Sontacchi for all parameters | `orbit_formula`, `cycle_equation`, `cycle_equation_sub` | 520 fuzz instances incl. 60-digit params; exact on all 86 committed positive-c cycles |
| cycles above the drift line | `cycle_expansion` (2^H > a^k) | holds on all 86 committed cycles |
| repulsion (dual of absorption) | `repel_orbit`, `collatz_avoids_3Z` | 300 systems x 200 steps, 0 violations |
| coset confinement mod a | `orbit_coset`, `sevenX1_iterates_mod7` | 200 systems fuzzed; all committed (7,c) cycle members in c*<2> mod 7 |
| finite Terras descent | `U_affine`, `descent`, `descent_all`, `countGood_8/16/20` | 800 fuzz instances; counts recomputed exactly |

## Certified good-residue densities (descent within k shortcut steps, n >= 8^k)

| level k | good residues | of 2^k | density | max weight |
|---:|---:|---:|---:|---:|
| 8 | 219 | 256 | 85.5469% | 5 |
| 16 | 58651 | 65536 | 89.4943% | 10 |
| 20 | 910596 | 1048576 | 86.8412% | 12 |

Density -> 1 as k -> infinity is Terras (1976); each finite level above is a
machine-certified theorem about ALL n >= 8^k in the counted classes.
