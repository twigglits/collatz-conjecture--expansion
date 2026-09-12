# Adaptive residue exploration

This note describes `src/residue.rs`. Numeric results below are discovery output
until independently reproduced by Lean; Rust and Python agreement alone is not
the repository's required mathematical certificate.

The goal is to exclude entire infinite residue classes from being a least
positive Collatz counterexample. For the shortcut map
`U(n) = (3n+1)/2` on odd inputs and `n/2` on even inputs, a node represents

`U^k(2^k q + r) = A q + b`, with `0 <= r < 2^k`.

Here `A = 3^s`, where `s` counts odd shortcut steps, and `b = U^k(r)`.
Splitting the high part into `2q+t`, for `t` in `{0,1}`, gives the child
residue `r+t*2^k`. Write `v=b+t*A`. The child's coefficient is `A` if `v` is
even and `3*A` if `v` is odd; its constant is `U(v)`.

If `A < M = 2^k`, the exact strict descent threshold is

`q0 = max(0, floor((b-r)/(M-A)) + 1)`.

The subtraction in this display is signed. The implementation avoids signed
conversion: return zero when `b < r`; otherwise divide the nonnegative
difference and add one. Equality requires the extra one: it is not descent.

A node closes only if `q0=0`, or `q0=1` with `r<=1`. Then every represented
integer greater than 1 strictly descends within `k` shortcut steps; the possible
finite exceptions are the excluded input zero and the terminal input one. A
coefficient drop with any exception greater than 1 is recorded diagnostically
and the actual tree continues branching. Its class is never silently assumed
to converge. Descent is itself only a reduction to a smaller starting integer,
not a standalone proof that the entire class converges.

The complete adaptive tree has a fixed requested maximum depth. A closed node
at depth `k` contributes `2^(D-k)` classes to coverage modulo `2^D`. The remaining
leaves are explicit unresolved classes at depth `D`. The count therefore
allows descent at any prefix, unlike the previous check restricted to the
single final depth.

## API and resource bounds

- `explore(max_depth: u32, node_budget: u64)` returns a `ResidueSummary`, or an
  explicit error if the traversal cannot complete under its limits.
- `coefficient_frontier(max_depth: u32)` returns a compressed coefficient-only
  count at each depth. Its counts do not inspect affine constants or finite
  exceptions, so they are not substitutes for the full closure check.
- Depth is capped at 63. All potentially overflowing affine arithmetic uses
  checked `u128` operations. Counts use checked additions and depth-bounded
  `u64` powers of two. An overflow produces an error, never a successful count.
- DFS stack storage is proportional to depth. The output stores aggregate
  counts, at most eight nontrivial exception samples, and at most 1,024 distinct
  threshold buckets. More threshold buckets cause an explicit error.
- No list of millions of residues is retained or exported. A Lean verifier can
  regenerate the tree and independently check the aggregate certificate.

The coefficient DP is possible because `A` is odd: the two child constants
`b` and `b+A` have opposite parity. Each live path has one child with coefficient
`A` and one with coefficient `3*A`. Grouping by odd-step count counts paths
satisfying `3^s >= 2^k` at every prefix, with quadratic rather than exponential
state storage/time in the maximum depth. This explains the DP recurrence;
a formal counting argument is still required for a mathematical claim.

## Discovery runs

Both full affine runs used a 5,000,000-node budget and finished successfully.
The Rust search checked the exact whole-class guard at every visited node.

| Maximum depth | Visited nodes | Total classes | Closed classes | Unresolved classes | Nontrivial first-drop exceptions |
|---:|---:|---:|---:|---:|---:|
| 24 | 735,399 | 16,777,216 | 16,490,635 | 286,581 | 0 |
| 26 | 2,454,885 | 67,108,864 | 66,071,490 | 1,037,374 | 0 |

The first-drop threshold histograms were:

- Depth 24: 81,117 nodes with `q0=0`, two with `q0=1`.
- Depth 26: 190,067 nodes with `q0=0`, two with `q0=1`.

At both depths the two exceptional nodes were exactly
`(k,r,M,A,b)=(1,0,2,1,0)` and `(2,1,4,3,1)`. Their finite exceptions are zero
and one respectively. No other finite exception occurred.

The compressed coefficient-only count at depth 32 was 41,347,483 survivors
out of 4,294,967,296 parity/residue paths. The full affine closure check was
not run to depth 32, so this number alone does not certify whole-class coverage
there.

Six tests passed in an isolated optimized Rust harness: strict threshold
boundaries, direct shortcut iteration against affine children, direct small
residue descent against the adaptive tree, DP/tree count agreement through
depth 20, depth-20 diagnostic values, and explicit budget/overflow failures.
The full-depth runs used that same source module. A subsequent resource guard
only caps the threshold histogram; the observed histograms use two buckets.

No finite depth completes a proof. For example, residue `2^D-1` has an all-odd
shortcut prefix of length `D`, so bounded-depth coefficient tables necessarily
leave survivors. Showing that every fixed positive integer eventually leaves
the unresolved set remains the missing global argument.
