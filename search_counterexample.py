#!/usr/bin/env python3
"""Target standard positive Collatz counterexamples with exact integers.

Python discovers finite trajectories; CollatzSearchCerts.lean independently
replays every successful trajectory and validates the reported metrics. Run:
    python3 search_counterexample.py --verify-lean
No machine-word window, probabilistic primality, or external convergence bound
is used. A fuel timeout remains unresolved, never a counterexample. The Lean
batch computation uses native_decide (generated native axioms), explicitly recorded
in the output. The soundness theorem itself has no axioms.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from collections import Counter

ROOT = Path(__file__).resolve().parent
FUEL = 300_000
BITS = (72, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096)
OFFSETS = (1, 3, 5, 7, 9, 15, 31, 63, 127, 255, 511, 1023)
PREFIX_BITS = (72, 128, 256, 512, 1024, 2048, 4096, 8192)
CRITICAL_BITS = (128, 256, 512, 1024, 2048, 4096, 8192)
HIGH_PARTS = (1, 3, 5, 7, 11, 27, 31, 63)
FAMILIES = ("power_offsets", "all_odd_prefix", "critical_parity_prefix", "hash_control")


def step(n: int) -> int:
    return 3 * n + 1 if n & 1 else n // 2


def critical_residue(length: int) -> tuple[int, int]:
    """Prescribe shortcut parity with 3**odd_count >= 2**k at each prefix.

    At level k, changing r to r+2**k flips the parity of U**k(r),
    since its affine slope is the odd number 3**odd_count. This constructs
    the unique residue modulo 2**length realizing the selected parity word.
    All prefix slopes are >=1, so the positive affine constant precludes
    descent through these prescribed shortcut steps. Lean independently
    checks each actual start's first descent, without trusting this argument.
    """
    residue = value = ones = 0
    modulus = slope = 1
    for _ in range(length):
        want_odd = slope < 2 * modulus
        if bool(value & 1) != want_odd:
            residue += modulus
            value += slope
        if want_odd:
            value = (3 * value + 1) // 2
            slope *= 3
            ones += 1
        else:
            value //= 2
        modulus *= 2
    return residue, ones


def seeds() -> list[dict]:
    rows: list[dict] = []
    seen: set[int] = set()

    def add(family: str, label: str, n: int, expr: str,
            prescribed_shortcut_steps: int = 0,
            prescribed_standard_steps: int = 0) -> None:
        if n in seen:
            return
        assert n > 2**71 and n & 1
        seen.add(n)
        rows.append({"family": family, "label": label, "start": n,
                     "lean_expression": expr,
                     "prescribed_shortcut_steps": prescribed_shortcut_steps,
                     "prescribed_standard_steps": prescribed_standard_steps})

    for bits in BITS:
        for offset in OFFSETS:
            for sign in (-1, 1):
                op = "+" if sign > 0 else "-"
                add("power_offsets", f"2^{bits}{op}{offset}",
                    2**bits + sign * offset, f"2 ^ {bits} {op} {offset}")
    for bits in PREFIX_BITS:
        for q in HIGH_PARTS:
            add("all_odd_prefix", f"{q}*2^{bits}-1", q * 2**bits - 1,
                f"{q} * 2 ^ {bits} - 1", bits, 2 * bits)
    for length in CRITICAL_BITS:
        residue, ones = critical_residue(length)
        for q in HIGH_PARTS:
            add("critical_parity_prefix", f"critical({length})+{q}*2^{length}",
                residue + q * 2**length, f"{residue} + {q} * 2 ^ {length}",
                length, length + ones)
    for bits in BITS:
        for index in range(64):
            tag = f"collatz-counterexample-search-v1:{bits}:{index}".encode()
            raw = int.from_bytes(hashlib.shake_256(tag).digest((bits + 7) // 8), "big")
            n = (raw & ((1 << bits) - 1)) | (1 << (bits - 1)) | 1
            add("hash_control", f"shake256({bits},{index})", n, str(n))
    return rows


def trace(n: int, fuel: int) -> dict:
    """Exact ordinary-step trajectory, with constant-memory Brent detection."""
    if n < 1 or fuel < 0:
        raise ValueError("positive start and nonnegative fuel required")
    start = peak = anchor = n
    first_descent = 0
    power, period = 1, 0
    if n == 1:
        return {"status": "reached_one", "steps": 0, "peak_bits": 1,
                "first_descent": 0}
    for elapsed in range(1, fuel + 1):
        n = step(n)
        peak = max(peak, n)
        if not first_descent and n < start:
            first_descent = elapsed
        if n == 1:
            return {"status": "reached_one", "steps": elapsed,
                    "peak_bits": peak.bit_length(), "first_descent": first_descent}
        period += 1
        if n == anchor:
            # A genuine repeat is evidence of a nontrivial cycle, but the
            # generated convergence certificate intentionally does not certify it.
            return {"status": "cycle_candidate_requires_certificate", "steps": elapsed,
                    "cycle_value": str(n), "cycle_period": period,
                    "peak_bits": peak.bit_length(), "first_descent": first_descent}
        if period == power:
            anchor, period, power = n, 0, 2 * power
    return {"status": "unresolved_fuel", "steps": fuel, "last_value": str(n),
            "peak_bits": peak.bit_length(), "first_descent": first_descent}


def summary(rows: list[dict]) -> dict:
    good = [r for r in rows if r["status"] == "reached_one"]
    return {"cases": len(rows), "status_counts": dict(Counter(r["status"] for r in rows)),
            "min_start_bits": min(r["start"].bit_length() for r in rows),
            "max_start_bits": max(r["start"].bit_length() for r in rows),
            "certified_trajectory_metrics": {
                "cases": len(good), "total_steps": sum(r["steps"] for r in good),
                "max_steps": max((r["steps"] for r in good), default=0),
                "max_peak_bits": max((r["peak_bits"] for r in good), default=0),
                "max_first_descent": max((r["first_descent"] for r in good), default=0)},
            "longest_trajectory": max(good, key=lambda r: r["steps"])["label"] if good else None,
            "latest_first_descent": max(good, key=lambda r: r["first_descent"])["label"] if good else None}


LEAN_HEADER = '''/-
GENERATED by search_counterexample.py; standard positive 3n+1 only.
Run: lean +leanprover/lean4:v4.31.0 CollatzSearchCerts.lean

Each row certifies an EXACT trajectory to 1 and its recorded metrics, with no
appeal to previously verified ranges. Nat is arbitrary precision. Metrics use
ordinary steps: odd n -> 3*n+1, even n -> n/2. All starts exceed 2^71.
The universal checker-soundness proof is kernel-only and has no axioms.
The finite batch and numeric summaries use native_decide / generated native axioms:
the compiler and native runtime are in their trusted computing base.
This finite dataset does not prove the Collatz conjecture.
-/
namespace CollatzSearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def step (n : Nat) : Nat := if n % 2 = 1 then 3 * n + 1 else n / 2

def iterate : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate k (step n)

structure State where
  value : Nat
  peak : Nat
  elapsed : Nat := 0
  firstDescent : Nat := 0
  firstOne : Nat := 0

def tick (start : Nat) (s : State) : State :=
  let value := step s.value
  let elapsed := s.elapsed + 1
  { value := value, peak := max s.peak value, elapsed := elapsed,
    firstDescent := if s.firstDescent = 0 ∧ value < start then elapsed else s.firstDescent,
    firstOne := if s.firstOne = 0 ∧ value = 1 then elapsed else s.firstOne }

def scan (start : Nat) : Nat → State → State
  | 0, s => s
  | k + 1, s => scan start k (tick start s)

structure Row where
  start : Nat
  steps : Nat
  peakBits : Nat
  firstDescent : Nat
  prescribedStandardSteps : Nat

def initial (n : Nat) : State := { value := n, peak := n }

def verifyRow (r : Row) : Bool :=
  let s := scan r.start r.steps (initial r.start)
  decide (2 ^ 71 < r.start ∧ s.value = 1 ∧ s.firstOne = r.steps ∧
    s.peak.log2 + 1 = r.peakBits ∧ s.firstDescent = r.firstDescent ∧
    r.prescribedStandardSteps < s.firstDescent)

theorem scan_value : ∀ (k start : Nat) (s : State),
    (scan start k s).value = iterate k s.value
  | 0, _, _ => rfl
  | k + 1, start, s => scan_value k start (tick start s)

/-- A successful checker result implies actual convergence for the stated map. -/
theorem verifyRow_sound (r : Row) (h : verifyRow r = true) :
    ∃ k, iterate k r.start = 1 := by
  have hv : (scan r.start r.steps (initial r.start)).value = 1 :=
    (of_decide_eq_true h).2.1
  exact ⟨r.steps, by simpa [scan_value, initial] using hv⟩

'''


def generate_lean(rows: list[dict]) -> str:
    good = [r for r in rows if r["status"] == "reached_one"]
    out = [LEAN_HEADER]
    groups = []
    for family in FAMILIES:
        group = [r for r in good if r["family"] == family]
        groups.append(family)
        out.append(f"def {family} : List Row := [\n")
        for i, row in enumerate(group):
            # Label is emitted only as a comment, never executable Lean syntax.
            out.append(f"  -- {row['label']}\n")
            out.append("  ⟨" + row["lean_expression"] + ", " +
                       ", ".join(str(row[k]) for k in
                                 ("steps", "peak_bits", "first_descent", "prescribed_standard_steps")) +
                       "⟩" + ("," if i + 1 < len(group) else "") + "\n")
        out.append("]\n\n")
        out.append(f"theorem {family}_verified : {family}.all verifyRow = true := by native_decide\n\n")
    out.append("def cases : List Row := " + " ++ ".join(groups) + "\n\n")
    out.append("theorem cases_verified : cases.all verifyRow = true := by\n")
    out.append("  simp only [cases, List.all_append, " + ", ".join(g + "_verified" for g in groups) +
               ", Bool.and_self]\n\n")
    out.append('''/-- Every row in this explicit dataset reaches 1; no finite-window assumption. -/
theorem certified_cases_converge (r : Row) (h : r ∈ cases) :
    ∃ k, iterate k r.start = 1 :=
  verifyRow_sound r (List.all_eq_true.mp cases_verified r h)

def metrics (rs : List Row) : List Nat :=
  [rs.length,
   rs.foldl (fun acc r => acc + r.steps) 0,
   rs.foldl (fun acc r => max acc r.steps) 0,
   rs.foldl (fun acc r => max acc r.peakBits) 0,
   rs.foldl (fun acc r => max acc r.firstDescent) 0,
   rs.foldl (fun acc r => max acc (r.start.log2 + 1)) 0,
   rs.foldl (fun acc r => min acc (r.start.log2 + 1)) 1000000]

''')
    for group in ["cases"] + groups:
        group_rows = good if group == "cases" else [r for r in good if r["family"] == group]
        if group_rows:
            s = summary(group_rows)
            m = s["certified_trajectory_metrics"]
            values = [m["cases"], m["total_steps"], m["max_steps"], m["max_peak_bits"],
                      m["max_first_descent"], s["max_start_bits"], s["min_start_bits"]]
        else:
            values = [0, 0, 0, 0, 0, 0, 1000000]
        out.append(f"theorem {group}_metrics : metrics {group} = {values} := by native_decide\n")
    out.append('''
#print axioms scan_value
#print axioms verifyRow_sound
#print axioms cases_verified
#print axioms certified_cases_converge
#print axioms cases_metrics
end CollatzSearch
''')
    return "".join(out)


def self_checks() -> None:
    assert trace(27, 200) == {"status": "reached_one", "steps": 111,
                            "peak_bits": 14, "first_descent": 96}
    assert trace(27, 95)["status"] == "unresolved_fuel"
    assert trace(1, 0)["status"] == "reached_one"
    assert trace(3, 0)["status"] == "unresolved_fuel"
    for length in range(1, 32):
        residue, ones = critical_residue(length)
        start = value = residue + 2**length
        counted = 0
        for _ in range(length):
            counted += value & 1
            value = (3 * value + 1) // 2 if value & 1 else value // 2
            assert value >= start
        assert counted == ones


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-lean", action="store_true", help="independently replay certificates in Lean")
    parser.add_argument("--fuel", type=int, default=FUEL, help="ordinary steps per input; exhausted fuel is unresolved")
    args = parser.parse_args()
    if args.fuel < 0:
        parser.error("fuel must be nonnegative")
    self_checks()
    rows = seeds()
    for index, row in enumerate(rows, 1):
        row.update(trace(row["start"], args.fuel))
        if index % 200 == 0:
            print(f"Searched {index}/{len(rows)} starts", flush=True)
    source = generate_lean(rows)
    lean_file = ROOT / "CollatzSearchCerts.lean"
    lean_file.write_text(source)
    data = {"schema": 1, "map": "odd n -> 3*n+1; even n -> n/2; positive integers",
            "fuel_ordinary_steps": args.fuel, "integer_arithmetic": "arbitrary precision",
            "coverage": "explicit structured and deterministic hash-derived starts only; not an interval",
            "certificate_status": "not_run", "certificate_trust": "native_decide / generated native axioms; Lean compiler and runtime",
            "certificate_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "summary": summary(rows),
            "families": {f: summary([r for r in rows if r["family"] == f]) for f in FAMILIES},
            "rows": [{**r, "start": str(r["start"])} for r in rows]}
    output = ROOT / "results" / "counterexample_search.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(data, indent=2) + "\n")
    if args.verify_lean:
        cmd = ["lean", "+leanprover/lean4:v4.31.0", str(lean_file)]
        print("Replaying all successful trajectories in Lean 4.31.0...", flush=True)
        version = subprocess.run(cmd[:2] + ["--version"], capture_output=True, text=True, check=True)
        checked = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        log = "Command: " + " ".join(cmd) + "\n" + version.stdout + checked.stdout + checked.stderr
        (ROOT / "results" / "counterexample_search.log").write_text(log)
        data["certificate_status"] = "verified" if checked.returncode == 0 else "failed"
        data["lean_version"] = version.stdout.strip()
        output.write_text(json.dumps(data, indent=2) + "\n")
        if checked.returncode:
            print(log, file=sys.stderr)
            raise SystemExit(checked.returncode)
    print(json.dumps({"certificate_status": data["certificate_status"], "summary": data["summary"],
                      "families": data["families"]}, indent=2))


if __name__ == "__main__":
    main()
