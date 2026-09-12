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

/// Inspect the verifier's output, without treating filenames in our log as diagnostics.
pub fn lean_proof_succeeded(output: &std::process::Output) -> bool {
    output.status.success()
        && [&output.stdout, &output.stderr].into_iter().all(|bytes| {
            let text = String::from_utf8_lossy(bytes);
            !text.contains("sorryAx") && !text.contains("declaration uses 'sorry'")
        })
}

/// Compare existing file targets, including symlinks and Unix hard links.
/// A missing path cannot alias an existing input; other filesystem errors propagate.
pub fn same_existing_file(
    left: &std::path::Path,
    right: &std::path::Path,
) -> std::io::Result<bool> {
    let metadata = |path| match std::fs::metadata(path) {
        Ok(meta) => Ok(Some(meta)),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(error),
    };
    let (Some(left_meta), Some(right_meta)) = (metadata(left)?, metadata(right)?) else {
        return Ok(false);
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        Ok(left_meta.dev() == right_meta.dev() && left_meta.ino() == right_meta.ino())
    }
    #[cfg(not(unix))]
    {
        let _ = (left_meta, right_meta);
        Ok(left.canonicalize()? == right.canonicalize()?)
    }
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
