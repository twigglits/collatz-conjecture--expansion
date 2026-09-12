# Lean 4.33.1 verification

The official [latest stable release](https://github.com/leanprover/lean4/releases/tag/v4.33.1)
was checked on 13 September 2026 (Africa/Johannesburg). The compiler reports:

```text
Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

All **19 existing standalone proof and certificate files passed**, with no compiler
warnings or admitted-proof dependencies reported:

- [structural.json](structural.json): 14 top-level standalone files, with
  commands, source hashes, version, durations, and individual logs.
- [certificates.json](certificates.json): five existing generated certificates,
  including the Python and Rust trajectory certificates, the depth-26 residue
  certificate, and both historical analysis certificates. Their sources were
  checked without regeneration.

The partial templates in `lean/` are not standalone modules. Their composed
proofs are covered by generated certificates and the Rust integration checks.

The toolchain upgrade preserves the trust distinction: structural kernel
proofs retain their standard logical dependencies; `CollatzFrontier.lean` also
contains native count checks, and generated certificates use `native_decide`
for large finite computations. Those computations still trust Lean's compiler
and runtime. Passing these files verifies their stated theorems and finite
search claims; it is not a proof of the full Collatz conjecture.

The repository's `lean-toolchain` now selects `leanprover/lean4:v4.33.1`.
Rust verification launchers embed that file at build time, and the Python
reference reads it when invoked. Current source instructions use the pin;
historical logs and saved generated-source headers retain their original
compiler provenance. Changing the pin requires rebuilding Rust.

```sh
elan toolchain install leanprover/lean4:v4.33.1
lean --version
lean CollatzCycleCriterion.lean
cargo test --locked
cargo test --locked --test residue_cli -- --ignored
```

The launchers were then tested with the new pin:

- All 38 active Rust tests passed; [Cargo log](integration/cargo-tests.log).
- The additional real-Lean integration test passed at residue depths 0, 1,
  and 8; [integration log](integration/residue-integration.log).
- A search with a 512-step limit generated and verified 33 trajectories,
  totaling 14,512 replayed steps. Its 1,224 fuel-limited cases remain
  unresolved. The [search manifest](integration/search/counterexample_search_rust.json)
  and [Lean log](integration/search/counterexample_search_rust.log) record the
  actual 4.33.1 selector and compiler version.
- Clippy with warnings denied and formatting checks passed for the changed
  Rust code.

The older 4.31.0 toolchain remains installed for reproducing historical runs.
