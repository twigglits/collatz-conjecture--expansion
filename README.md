# collatz-conjecture--expansion

An honest attempt at providing a proof for the Collatz-conjecture by means analyzing base collatz-conjecture, variations thereof and forming generalized statements.

**→ Read [REPORT.md](REPORT.md) for the full study, or the working academic paper: [COLLATZ-EXPANSION.md](COLLATZ-EXPANSION.md) / [COLLATZ-EXPANSION.pdf](COLLATZ-EXPANSION.pdf).**

Hard rule of this repo: every computational claim is backed by CUDA runs or Lean machine-verified proofs.

| File | Role |
|---|---|
| `COLLATZ-EXPANSION.md` / `.pdf` | Working paper (typeset via pandoc → pdflatex): machine-verified structure of f(x)=ax+c — theorems, certificates, drift law, cycle-equation mechanism |
| `collatz.cu` | CUDA sweep engine: cycle inventory (Brent) + mass orbit classification for `f(x)=ax+c` variants |
| `universal.cu` | CUDA verifier for the sharpened universal-cycle laws: rigidity grid (2.7e11 pairs), fixed-point census vs. the divisor law, universal-family catalog (all odd a < 2^24), scaling-identity fuzz |
| `CollatzTheory.lean` | General theorems, kernel-only proofs (parity reduction, scaling conjugacy, gcd absorption, universal cycle for a = 2^k−1 **and its converse**: master formula F(c) = odd(a+1)·c, one-step cycle law, orbit transport) |
| `CollatzCerts.lean` | Generated certificates: 89 cycle proofs (`decide`) + 38 range-classification proofs (`native_decide`) |
| `analyze.py` | Exact-arithmetic cross-checks of GPU output; generates `CollatzCerts.lean` |
| `verify_universal.py` | Exact big-integer layer for `universal.cu`: catalog re-iteration, law set-equality, 350-digit stress instances |
| `results/` | Raw sweep JSON, summary tables, logs |

Quick start: see §7 of [REPORT.md](REPORT.md).
