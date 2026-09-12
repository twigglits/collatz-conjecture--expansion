//! Generate a Lean replay certificate without trusting the Rust search result.

use std::fmt::Write;

use num_bigint::BigUint;

use crate::{Row, seeds::FAMILIES};

const LEAN_HEADER: &str = include_str!("../lean/SearchCertificateHeader.lean");

const LEAN_SOUNDNESS_AND_METRICS: &str = r#"/-- Every row in this explicit dataset reaches 1; no finite-window assumption. -/
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

"#;

const LEAN_FOOTER: &str = r#"
#print axioms scan_value
#print axioms verifyRow_sound
#print axioms cases_verified
#print axioms certified_cases_converge
#print axioms cases_metrics
end CollatzSearch
"#;

/// Produce the independently replayed Lean dataset and its numeric summaries.
///
/// Only trajectories that reached one enter the certificate. Fuel exhaustion
/// and cycle candidates remain absent from convergence claims. An empty
/// successful subset still produces a valid empty-dataset certificate.
pub fn generate_lean(rows: &[Row]) -> String {
    let good: Vec<&Row> = rows
        .iter()
        .filter(|row| row.trace.status == "reached_one")
        .collect();
    let mut out = String::from(LEAN_HEADER);

    for family in FAMILIES.iter().copied() {
        let group: Vec<&Row> = good
            .iter()
            .copied()
            .filter(|row| row.seed.family == family)
            .collect();
        writeln!(out, "def {family} : List Row := [").unwrap();
        for (index, row) in group.iter().enumerate() {
            // Prefix every line, so a multiline label remains a Lean comment.
            for line in row.seed.label.split('\n') {
                writeln!(out, "  -- {line}").unwrap();
            }
            writeln!(
                out,
                "  ⟨{}, {}, {}, {}, {}⟩{}",
                row.seed.lean_expression,
                row.trace.steps,
                row.trace.peak_bits,
                row.trace.first_descent,
                row.seed.prescribed_standard_steps,
                if index + 1 < group.len() { "," } else { "" },
            )
            .unwrap();
        }
        out.push_str("]\n\n");
        writeln!(
            out,
            "theorem {family}_verified : {family}.all verifyRow = true := by native_decide\n"
        )
        .unwrap();
    }

    writeln!(out, "def cases : List Row := {}\n", FAMILIES.join(" ++ ")).unwrap();
    out.push_str("theorem cases_verified : cases.all verifyRow = true := by\n");
    let group_theorems = FAMILIES
        .iter()
        .map(|family| format!("{family}_verified"))
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(
        out,
        "  simp only [cases, List.all_append, {group_theorems}, Bool.and_self]\n"
    )
    .unwrap();
    out.push_str(LEAN_SOUNDNESS_AND_METRICS);

    write_metrics(&mut out, "cases", &good);
    for family in FAMILIES.iter().copied() {
        let group: Vec<&Row> = good
            .iter()
            .copied()
            .filter(|row| row.seed.family == family)
            .collect();
        write_metrics(&mut out, family, &group);
    }
    out.push_str(LEAN_FOOTER);
    out
}

fn write_metrics(out: &mut String, name: &str, rows: &[&Row]) {
    let mut total_steps = BigUint::default();
    let mut max_steps = 0;
    let mut max_peak_bits = 0;
    let mut max_first_descent = 0;
    let mut max_start_bits = 0;
    let mut min_start_bits = None;
    for row in rows {
        total_steps += row.trace.steps;
        max_steps = max_steps.max(row.trace.steps);
        max_peak_bits = max_peak_bits.max(row.trace.peak_bits);
        max_first_descent = max_first_descent.max(row.trace.first_descent);
        let bits = row.seed.start.bits();
        max_start_bits = max_start_bits.max(bits);
        min_start_bits = Some(min_start_bits.map_or(bits, |minimum: u64| minimum.min(bits)));
    }
    writeln!(
        out,
        "theorem {name}_metrics : metrics {name} = [{}, {total_steps}, {max_steps}, {max_peak_bits}, {max_first_descent}, {max_start_bits}, {}] := by native_decide",
        rows.len(),
        min_start_bits.unwrap_or(1_000_000),
    )
    .unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Seed, search::Trace};

    fn row(family: &'static str, label: &str, status: &str) -> Row {
        Row {
            seed: Seed {
                family,
                label: label.to_owned(),
                start: (BigUint::from(1_u8) << 72_usize) + 1_u8,
                lean_expression: "2 ^ 72 + 1".to_owned(),
                prescribed_shortcut_steps: 3,
                prescribed_standard_steps: 5,
            },
            trace: Trace {
                status: status.to_owned(),
                steps: 17,
                peak_bits: 74,
                first_descent: 9,
                last_value: None,
                cycle_value: None,
                cycle_period: None,
            },
        }
    }

    #[test]
    fn certificate_excludes_unresolved_and_cycle_candidates() {
        let rows = [
            row("power_offsets", "successful", "reached_one"),
            row("hash_control", "fuel-boundary", "unresolved_fuel"),
            row(
                "hash_control",
                "cycle-boundary",
                "cycle_candidate_requires_certificate",
            ),
        ];
        let source = generate_lean(&rows);
        assert!(source.contains("  -- successful\n  ⟨2 ^ 72 + 1, 17, 74, 9, 5⟩\n"));
        assert!(!source.contains("fuel-boundary"));
        assert!(!source.contains("cycle-boundary"));
        assert!(source.contains(
            "theorem cases_metrics : metrics cases = [1, 17, 17, 74, 9, 73, 73] := by native_decide"
        ));
        assert!(source.contains("theorem certified_cases_converge"));
    }

    #[test]
    fn empty_successful_subset_has_zero_metrics_and_all_groups() {
        let rows = [row("power_offsets", "zero-fuel", "unresolved_fuel")];
        let source = generate_lean(&rows);
        assert_eq!(source, generate_lean(&[]));
        for name in std::iter::once("cases").chain(FAMILIES.iter().copied()) {
            assert!(source.contains(&format!("theorem {name}_metrics : metrics {name} = [0, 0, 0, 0, 0, 0, 1000000] := by native_decide")));
        }
        for family in FAMILIES {
            assert!(source.contains(&format!("def {family} : List Row := [\n]\n\n")));
            assert!(source.contains(&format!("theorem {family}_verified")));
        }
    }

    #[test]
    fn step_totals_do_not_overflow_machine_integers() {
        let mut first = row("power_offsets", "first", "reached_one");
        first.trace.steps = u64::MAX;
        let mut second = row("hash_control", "second", "reached_one");
        second.trace.steps = u64::MAX;
        let source = generate_lean(&[first, second]);
        assert!(source.contains(
            "metrics cases = [2, 36893488147419103230, 18446744073709551615, 74, 9, 73, 73]"
        ));
    }

    #[test]
    fn group_order_and_relative_row_order_are_preserved() {
        let rows = [
            row("hash_control", "hash-first-input", "reached_one"),
            row("power_offsets", "power-first", "reached_one"),
            row("power_offsets", "power-second", "reached_one"),
        ];
        let source = generate_lean(&rows);
        let first = source.find("  -- power-first\n").unwrap();
        let second = source.find("  -- power-second\n").unwrap();
        let last = source.find("  -- hash-first-input\n").unwrap();
        assert!(first < second && second < last);
        assert!(source.contains("  -- power-first\n  ⟨2 ^ 72 + 1, 17, 74, 9, 5⟩,\n"));
        assert!(source.contains("  -- power-second\n  ⟨2 ^ 72 + 1, 17, 74, 9, 5⟩\n"));
    }

    #[test]
    fn multiline_labels_remain_comments() {
        let source = generate_lean(&[row(
            "power_offsets",
            "first line\nsecond line",
            "reached_one",
        )]);
        assert!(source.contains("  -- first line\n  -- second line\n"));
    }
}
