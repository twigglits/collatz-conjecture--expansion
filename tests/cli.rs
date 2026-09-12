use serde_json::Value;
use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_DIR: AtomicU64 = AtomicU64::new(0);

struct TempDir(PathBuf);
impl TempDir {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "collatz-cli-{}-{}",
            std::process::id(),
            NEXT_DIR.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).expect("create isolated test output");
        Self(path)
    }
    fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_collatz-search"));
        command
            .current_dir(&self.0)
            .args(["--output-dir", "out", "--certificate", "Test.lean"]);
        command
    }
    fn manifest(&self) -> Value {
        serde_json::from_slice(
            &fs::read(self.0.join("out/counterexample_search_rust.json")).unwrap(),
        )
        .unwrap()
    }
}
impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn parallel_cli_matches_every_certified_python_row() {
    let output = TempDir::new();
    let run = output.command().args(["--threads", "8"]).output().unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let actual = output.manifest();
    let baseline: Value =
        serde_json::from_str(include_str!("../results/counterexample_search.json")).unwrap();
    for key in ["rows", "summary", "families"] {
        assert_eq!(actual[key], baseline[key], "{key}");
    }
    assert_eq!(actual["worker_count"], 8);
    assert_eq!(actual["certificate_status"], "not_run");
    let certificate = fs::read_to_string(output.0.join("Test.lean")).unwrap();
    let baseline_certificate = include_str!("../CollatzSearchCerts.lean");
    // Only Rust provenance and the default Run filename differ.
    assert_eq!(
        certificate.lines().skip(3).collect::<Vec<_>>(),
        baseline_certificate.lines().skip(3).collect::<Vec<_>>()
    );
}

#[test]
fn zero_fuel_stays_unresolved_and_output_collision_preserves_manifest() {
    let output = TempDir::new();
    let run = output
        .command()
        .args(["--fuel", "0", "--threads", "4"])
        .output()
        .unwrap();
    assert!(run.status.success());
    let original = output.manifest();
    assert_eq!(
        original["summary"]["status_counts"]["unresolved_fuel"],
        1257
    );
    assert_eq!(
        original["summary"]["certified_trajectory_metrics"]["cases"],
        0
    );
    let bad = output
        .command()
        .args([
            "--fuel",
            "0",
            "--certificate",
            "out/counterexample_search_rust.json",
        ])
        .output()
        .unwrap();
    assert!(!bad.status.success());
    assert!(String::from_utf8_lossy(&bad.stderr).contains("must differ"));
    assert_eq!(output.manifest(), original);
}
