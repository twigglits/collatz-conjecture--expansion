# Mechanical-word defect diagnostics

These files are **unverified diagnostic observations** from exact Rust
arithmetic. They have no Lean or CUDA certificate and must not be promoted
to certified finite exclusions or a universal nonexistence claim. The
mathematical descriptions below explain what was computed; the tests check
implementation agreement, not a formal proof of the program.

The executable is [`src/bin/cycle-defects.rs`](../../src/bin/cycle-defects.rs).
It uses `BigUint` throughout all mathematical arithmetic. For each requested
integer `k`, it computes `3^k` and sets `H` to its exact bit length. Since
`3^k` is not a power of two, this is exactly `ceil(k log_2 3)`; no floating
point determines a word or a divisibility result. It generates

\[
 h_i=\lfloor(i+1)H/k\rfloor-\lfloor iH/k\rfloor,
 \qquad D=2^H-3^k.
\]

Both mutations transfer one halving unit from a symbol 2 to its successor.
For `22 -> 13`, the transfer starts at the first 2. For `121 -> 112`, it
starts at the middle 2. If `W_j` is the original numerator at that cyclic
starting point, the mutated numerator is

\[
 W'_j=W_j-2\cdot3^{k-2}.
\]

Only the first proper prefix changes. Original rotations satisfy

\[
 2^{h_j}W_{j+1}=3W_j+D.
\]

The program therefore keeps `W_j mod D`, rotates it by multiplying by 3 and
halving modulo the odd `D`, and computes `gcd(D, W'_j)` with binary gcd.
The reduced denominator is exactly `D/gcd(D,W'_j)`; it is 1 exactly when the
mutated numerator passes the integer-cycle divisibility test.

When `g=gcd(k,H)>1`, the original word has period `p=k/g`. The program
generates that shorter block and scales its numerator by

\[
 \frac{2^H-3^k}{2^{H/g}-3^{k/g}}.
\]

It evaluates its `p` distinct rotations and counts each result with
multiplicity `g`. Thus completed rows cover every original cyclic position,
including mutations that cross the array boundary. This reuse and the
modular recurrence avoid recomputing a length-`k` numerator at each position.

Each `periods.jsonl` row includes exact gcd histograms for both mutation
types. The smallest reduced denominator in each family is recorded by bit
length and SHA256, with its exact gcd retained; `k,H` reconstruct `D`.
Summary files record the source hash and JSONL hash. Wall times describe
these diagnostic runs only.

| Run | Period lengths covered | Mutation positions | Observation |
| --- | --- | ---: | --- |
| [all-3-1000](all-3-1000/summary.json) | Every integer 3 through 1,000 | 207,228 | No integer candidate observed |
| [selected-1250-10000](selected-1250-10000/summary.json) | 1,250, 1,500, ..., 10,000 | 84,027 | No integer candidate observed |
| [k10007](k10007/summary.json) | 10,007; all 10,007 rotations | 4,153 | No integer candidate observed |

These three completed runs cover 1,035 period lengths and 295,408 mutation
positions. They do **not** cover every integer period through 10,007.
The separate [time-limit-smoke](time-limit-smoke/summary.json) run repeats a
partial subset of `k=10007` and is not included in those totals. It stopped
after its one-second budget, with `complete=false` and
`next_or_partial_k=10007`.

Gcds need not be 1. For example, the unverified `k=582,H=923` row contains
a `22 -> 13` candidate with gcd 82,727, leaving a 906-bit reduced denominator.
This diagnostic example is useful for checking proposed small-gcd claims,
but is not a Lean-certified arithmetic statement.

Four Rust tests pass: binary gcd versus an independent Euclidean algorithm;
exact bit-length and mechanical-period checks through 500; every mutation
at every cyclic position for `k=3..90` versus direct word reconstruction;
and modular rotation versus full numerators at `k=701`. The binary also
passes `cargo clippy --bin cycle-defects -- -D warnings`.

Example usage:

```sh
cargo build --release --bin cycle-defects
target/release/cycle-defects --min-k 3 --max-k 1000 --seconds 120 --output-dir results/cycle-defects/new-run
```

Output files are created with `create_new`; choose a new directory for each
run. The time limit is checked between rotations, so setup and an individual
arithmetic operation can finish after the deadline. Incomplete coverage is
reported explicitly and is never treated as an exclusion.
