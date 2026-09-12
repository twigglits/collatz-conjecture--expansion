//! Adaptive residue classes for the shortcut Collatz map U.
//!
//! A node records the exact identity
//! U^k(2^k*q + r) = a*q + b. A branch stops at its first a < 2^k.
//! Such a leaf descends for q >= q0, where q0 is the exact strict threshold.
//! Leaves with no exceptional n > 1 cover their whole positive class by
//! descent or the terminal value 1. Counts here are computational discovery;
//! an independent Lean checker must certify any mathematical claim made from
//! them. No coefficient-only count is presented as a full exception check.

use serde::Serialize;
use std::collections::BTreeMap;

const MAX_DEPTH: u32 = 63;
const EXCEPTION_SAMPLE_LIMIT: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct AffineNode {
    pub depth: u32,
    pub residue: u128,
    pub modulus: u128,
    pub coefficient: u128,
    pub constant: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ThresholdCount {
    pub q0: u128,
    pub leaves: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FiniteException {
    pub node: AffineNode,
    pub q0: u128,
    pub q: u128,
    pub start: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidueSummary {
    pub max_depth: u32,
    pub node_budget: u64,
    pub visited_nodes: u64,
    pub total_residues_at_max_depth: u64,
    /// Leaves reaching the depth limit without any coefficient drop.
    pub slope_survivors_at_max_depth: u64,
    /// Weighted first-drop leaves, including any requiring finite exceptions.
    pub coefficient_drop_weight_at_max_depth: u64,
    /// Weighted leaves having no finite exception greater than 1.
    pub closed_positive_weight_at_max_depth: u64,
    /// Conservative complement of fully closed positive classes.
    pub unresolved_weight_at_max_depth: u64,
    pub first_drop_leaves_by_depth: Vec<u64>,
    pub q0_histogram: Vec<ThresholdCount>,
    pub nontrivial_exception_count: u128,
    /// At most eight examples, regardless of the total number of exceptions.
    pub exception_samples: Vec<FiniteException>,
    /// Leaves whose finite exceptions consist only of 0 or 1.
    pub trivial_exception_nodes: Vec<AffineNode>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CoefficientLevel {
    pub depth: u32,
    pub total_residues: u64,
    pub surviving_residues: u64,
    pub coefficient_drop_residues: u64,
    /// Counts by number of odd shortcut steps; these sum to surviving_residues.
    pub survivors_by_odd_count: Vec<u64>,
}

fn overflow(operation: &str) -> String {
    format!("exact residue arithmetic overflow during {operation}; no result certified")
}

fn add_count(target: &mut u64, value: u64) -> Result<(), String> {
    *target = target
        .checked_add(value)
        .ok_or_else(|| overflow("count addition"))?;
    Ok(())
}

fn root() -> AffineNode {
    AffineNode {
        depth: 0,
        residue: 0,
        modulus: 1,
        coefficient: 1,
        constant: 0,
    }
}

impl AffineNode {
    fn child(self, high_bit: bool) -> Result<Self, String> {
        let added_a = if high_bit { self.coefficient } else { 0 };
        let before = self
            .constant
            .checked_add(added_a)
            .ok_or_else(|| overflow("child intercept"))?;
        let odd = before & 1 == 1;
        let coefficient = if odd {
            self.coefficient
                .checked_mul(3)
                .ok_or_else(|| overflow("child coefficient"))?
        } else {
            self.coefficient
        };
        let constant = if odd {
            before
                .checked_mul(3)
                .and_then(|n| n.checked_add(1))
                .ok_or_else(|| overflow("shortcut numerator"))?
                / 2
        } else {
            before / 2
        };
        Ok(Self {
            depth: self.depth.checked_add(1).ok_or_else(|| overflow("depth"))?,
            residue: self
                .residue
                .checked_add(if high_bit { self.modulus } else { 0 })
                .ok_or_else(|| overflow("child residue"))?,
            modulus: self
                .modulus
                .checked_mul(2)
                .ok_or_else(|| overflow("child modulus"))?,
            coefficient,
            constant,
        })
    }

    /// Smallest q0 for which a*q+b < modulus*q+residue for every q>=q0.
    /// None means there is no contracting affine coefficient at this node.
    pub fn descent_threshold(self) -> Result<Option<u128>, String> {
        if self.coefficient >= self.modulus {
            return Ok(None);
        }
        if self.constant < self.residue {
            return Ok(Some(0));
        }
        let gap = self.modulus - self.coefficient;
        let difference = self.constant - self.residue;
        Ok(Some(
            (difference / gap)
                .checked_add(1)
                .ok_or_else(|| overflow("strict threshold"))?,
        ))
    }
}

/// Explore first coefficient-drop classes with O(max_depth) stack storage.
///
/// The node budget is mandatory. Exceeding it or the checked arithmetic bounds
/// returns an error, rather than reporting a partial traversal as a complete
/// count. No orbit is assumed to converge merely because its coefficient drops:
/// every exceptional start greater than 1 is counted and prevents its leaf
/// from contributing to `closed_positive_weight_at_max_depth`.
pub fn explore(max_depth: u32, node_budget: u64) -> Result<ResidueSummary, String> {
    if max_depth > MAX_DEPTH {
        return Err(format!("max_depth must be at most {MAX_DEPTH}"));
    }
    if node_budget == 0 {
        return Err("node_budget must be positive".to_owned());
    }
    let total = 1_u64
        .checked_shl(max_depth)
        .ok_or_else(|| overflow("total residues"))?;
    let mut result = ResidueSummary {
        max_depth,
        node_budget,
        visited_nodes: 0,
        total_residues_at_max_depth: total,
        slope_survivors_at_max_depth: 0,
        coefficient_drop_weight_at_max_depth: 0,
        closed_positive_weight_at_max_depth: 0,
        unresolved_weight_at_max_depth: 0,
        first_drop_leaves_by_depth: vec![0; max_depth as usize + 1],
        q0_histogram: Vec::new(),
        nontrivial_exception_count: 0,
        exception_samples: Vec::new(),
        trivial_exception_nodes: Vec::new(),
    };
    let mut histogram = BTreeMap::<u128, u64>::new();
    let mut stack = Vec::with_capacity(max_depth as usize + 1);
    stack.push(root());
    while let Some(node) = stack.pop() {
        if result.visited_nodes >= node_budget {
            return Err(format!(
                "node budget {node_budget} exhausted before depth {max_depth} traversal completed"
            ));
        }
        add_count(&mut result.visited_nodes, 1)?;
        if let Some(q0) = node.descent_threshold()? {
            add_count(
                &mut result.first_drop_leaves_by_depth[node.depth as usize],
                1,
            )?;
            add_count(histogram.entry(q0).or_default(), 1)?;
            let weight = 1_u64
                .checked_shl(max_depth - node.depth)
                .ok_or_else(|| overflow("leaf residue weight"))?;
            add_count(&mut result.coefficient_drop_weight_at_max_depth, weight)?;
            // A residue is in [0,modulus), and modulus>=2 at a drop. Therefore
            // q=0 is the only possible exceptional start equal to 0 or 1.
            let first_nontrivial_q = u128::from(node.residue <= 1 && q0 > 0);
            let nontrivial = q0 - first_nontrivial_q;
            result.nontrivial_exception_count = result
                .nontrivial_exception_count
                .checked_add(nontrivial)
                .ok_or_else(|| overflow("exception count"))?;
            if nontrivial == 0 {
                add_count(&mut result.closed_positive_weight_at_max_depth, weight)?;
                if q0 > 0 {
                    result.trivial_exception_nodes.push(node);
                }
            } else {
                let mut q = first_nontrivial_q;
                while q < q0 && result.exception_samples.len() < EXCEPTION_SAMPLE_LIMIT {
                    let start = node
                        .modulus
                        .checked_mul(q)
                        .and_then(|n| n.checked_add(node.residue))
                        .ok_or_else(|| overflow("exception start"))?;
                    result
                        .exception_samples
                        .push(FiniteException { node, q0, q, start });
                    q = q
                        .checked_add(1)
                        .ok_or_else(|| overflow("exception sample index"))?;
                }
            }
        } else if node.depth == max_depth {
            add_count(&mut result.slope_survivors_at_max_depth, 1)?;
        } else {
            // LIFO order visits the lower child first and is deterministic.
            stack.push(node.child(true)?);
            stack.push(node.child(false)?);
        }
    }
    result.q0_histogram = histogram
        .into_iter()
        .map(|(q0, leaves)| ThresholdCount { q0, leaves })
        .collect();
    let partition = result
        .slope_survivors_at_max_depth
        .checked_add(result.coefficient_drop_weight_at_max_depth)
        .ok_or_else(|| overflow("partition check"))?;
    if partition != total {
        return Err(
            "internal error: adaptive leaves do not partition the requested residues".to_owned(),
        );
    }
    result.unresolved_weight_at_max_depth = total - result.closed_positive_weight_at_max_depth;
    Ok(result)
}

/// Compress the coefficient-only survivor count by odd-step count.
///
/// Every current affine coefficient is odd, so the two residue children have
/// opposite parity. Their coefficients are a and 3*a. This DP records paths
/// with 3^s >= 2^k at every prefix. It does NOT inspect affine constants or
/// prove that finite exceptions in the removed classes are harmless.
pub fn coefficient_frontier(max_depth: u32) -> Result<Vec<CoefficientLevel>, String> {
    if max_depth > MAX_DEPTH {
        return Err(format!("max_depth must be at most {MAX_DEPTH}"));
    }
    let mut powers = vec![1_u128];
    for _ in 0..max_depth {
        powers.push(
            powers
                .last()
                .unwrap()
                .checked_mul(3)
                .ok_or_else(|| overflow("power of three"))?,
        );
    }
    let mut counts = vec![1_u64];
    let mut levels = vec![CoefficientLevel {
        depth: 0,
        total_residues: 1,
        surviving_residues: 1,
        coefficient_drop_residues: 0,
        survivors_by_odd_count: counts.clone(),
    }];
    for depth in 1..=max_depth {
        let total = 1_u64
            .checked_shl(depth)
            .ok_or_else(|| overflow("DP total residues"))?;
        let mut next = vec![0_u64; depth as usize + 1];
        for (ones, count) in counts.iter().copied().enumerate() {
            for child_ones in [ones, ones + 1] {
                if powers[child_ones] >= u128::from(total) {
                    add_count(&mut next[child_ones], count)?;
                }
            }
        }
        let surviving = next.iter().try_fold(0_u64, |sum, count| {
            sum.checked_add(*count)
                .ok_or_else(|| overflow("DP survivor sum"))
        })?;
        levels.push(CoefficientLevel {
            depth,
            total_residues: total,
            surviving_residues: surviving,
            coefficient_drop_residues: total - surviving,
            survivors_by_odd_count: next.clone(),
        });
        counts = next;
    }
    Ok(levels)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shortcut(n: u128) -> u128 {
        if n & 1 == 1 {
            n.checked_mul(3).unwrap().checked_add(1).unwrap() / 2
        } else {
            n / 2
        }
    }

    #[test]
    fn strict_threshold_handles_equality_and_signed_difference() {
        let node = AffineNode {
            depth: 2,
            residue: 0,
            modulus: 4,
            coefficient: 3,
            constant: 2,
        };
        assert_eq!(node.descent_threshold().unwrap(), Some(3));
        assert_eq!(
            node.coefficient * 2 + node.constant,
            node.modulus * 2 + node.residue
        );
        assert!(node.coefficient * 3 + node.constant < node.modulus * 3 + node.residue);
        assert_eq!(
            AffineNode { residue: 3, ..node }
                .descent_threshold()
                .unwrap(),
            Some(0)
        );
        assert_eq!(
            AffineNode { residue: 2, ..node }
                .descent_threshold()
                .unwrap(),
            Some(1)
        );
        assert_eq!(
            AffineNode {
                coefficient: 4,
                ..node
            }
            .descent_threshold()
            .unwrap(),
            None
        );
    }

    #[test]
    fn residue_children_match_direct_shortcut_iteration() {
        let mut frontier = vec![root()];
        for _ in 0..8 {
            let mut next = Vec::new();
            for parent in frontier {
                for bit in [false, true] {
                    let node = parent.child(bit).unwrap();
                    assert!(node.residue < node.modulus);
                    assert!(node.coefficient & 1 == 1);
                    for q in [0, 1, 7, (1_u128 << 64) + 1] {
                        let start = node.modulus * q + node.residue;
                        let mut value = start;
                        for _ in 0..node.depth {
                            value = shortcut(value);
                        }
                        assert_eq!(value, node.coefficient * q + node.constant);
                    }
                    next.push(node);
                }
            }
            frontier = next;
        }
    }

    #[test]
    fn adaptive_classes_match_direct_descent_at_small_depth() {
        let depth = 10;
        let tree = explore(depth, 10_000).unwrap();
        let modulus = 1_u128 << depth;
        let mut direct_good = 0;
        for residue in 0..modulus {
            let start = modulus + residue;
            let mut value = start;
            for _ in 0..depth {
                value = shortcut(value);
                if value < start {
                    direct_good += 1;
                    break;
                }
            }
        }
        assert_eq!(tree.closed_positive_weight_at_max_depth, direct_good);
        assert_eq!(tree.nontrivial_exception_count, 0);
    }

    #[test]
    fn coefficient_compression_matches_affine_tree() {
        for level in coefficient_frontier(20).unwrap() {
            let tree = explore(level.depth, 100_000).unwrap();
            assert_eq!(level.surviving_residues, tree.slope_survivors_at_max_depth);
            assert_eq!(
                level.coefficient_drop_residues,
                tree.coefficient_drop_weight_at_max_depth
            );
        }
    }

    #[test]
    fn depth_twenty_first_drop_exceptions_are_only_zero_and_one() {
        let tree = explore(20, 100_000).unwrap();
        assert_eq!(tree.visited_nodes, 63_463);
        assert_eq!(tree.slope_survivors_at_max_depth, 27_328);
        assert_eq!(tree.closed_positive_weight_at_max_depth, 1_021_248);
        assert_eq!(tree.nontrivial_exception_count, 0);
        assert_eq!(
            tree.q0_histogram,
            [
                ThresholdCount {
                    q0: 0,
                    leaves: 4402
                },
                ThresholdCount { q0: 1, leaves: 2 }
            ]
        );
        assert_eq!(
            tree.trivial_exception_nodes
                .iter()
                .map(|n| n.residue)
                .collect::<Vec<_>>(),
            [0, 1]
        );
    }

    #[test]
    fn budgets_and_arithmetic_bounds_fail_explicitly() {
        assert!(explore(20, 100).unwrap_err().contains("budget"));
        assert!(explore(20, 0).is_err());
        assert!(explore(64, 100).is_err());
        assert!(coefficient_frontier(64).is_err());
        let bad = AffineNode {
            coefficient: u128::MAX,
            ..root()
        };
        assert!(bad.child(true).unwrap_err().contains("overflow"));
        assert_eq!(
            coefficient_frontier(63)
                .unwrap()
                .last()
                .unwrap()
                .total_residues,
            1_u64 << 63
        );
    }
}
