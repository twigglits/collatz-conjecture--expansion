use num_bigint::BigUint;
use serde::{Serialize, Serializer};

pub mod certificates;
pub mod residue;
pub mod search;
pub mod seeds;
pub mod verify_helpers;

/// The repository's Lean toolchain, embedded when this binary is built.
pub fn pinned_lean_toolchain() -> &'static str {
    include_str!("../lean-toolchain").trim()
}

#[derive(Clone, Debug, Serialize)]
pub struct Seed {
    pub family: &'static str,
    pub label: String,
    #[serde(serialize_with = "serialize_start")]
    pub start: BigUint,
    pub lean_expression: String,
    pub prescribed_shortcut_steps: u64,
    pub prescribed_standard_steps: u64,
}

fn serialize_start<S: Serializer>(n: &BigUint, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&n.to_string())
}

#[derive(Clone, Debug, Serialize)]
pub struct Row {
    #[serde(flatten)]
    pub seed: Seed,
    #[serde(flatten)]
    pub trace: search::Trace,
}
