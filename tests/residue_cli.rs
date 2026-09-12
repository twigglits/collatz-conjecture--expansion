use serde_json::Value;
use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Output(PathBuf);
impl Output {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "collatz-residue-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_residue-sieve"));
        command.current_dir(&self.0).args([
            "--depth",
            "8",
            "--output-dir",
            "out",
            "--certificate",
            "Residues.lean",
        ]);
        command
    }
}
impl Drop for Output {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn exact_partition_is_exported_but_unchecked_results_are_not_certified() {
    let temp = Output::new();
    let run = temp.command().output().unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let data: Value =
        serde_json::from_slice(&fs::read(temp.0.join("out/residue_sieve_rust.json")).unwrap())
            .unwrap();
    assert_eq!(data["certificate_status"], "not_run");
    let summary = &data["summary"];
    assert_eq!(summary["total_residues_at_max_depth"], 256);
    assert_eq!(
        summary["closed_positive_weight_at_max_depth"]
            .as_u64()
            .unwrap()
            + summary["unresolved_weight_at_max_depth"].as_u64().unwrap(),
        256
    );
    let source = fs::read_to_string(temp.0.join("Residues.lean")).unwrap();
    assert!(source.contains("theorem count_in_every_block"));
    assert!(source.contains("theorem accepted_starts_descend"));
    assert!(source.contains("countCovered 8 0 0 ="));
}

#[test]
fn exhausted_budget_and_output_collision_do_not_replace_prior_results() {
    let temp = Output::new();
    fs::create_dir(temp.0.join("out")).unwrap();
    let manifest = temp.0.join("out/residue_sieve_rust.json");
    fs::write(&manifest, "prior result").unwrap();
    let run = temp
        .command()
        .args(["--node-budget", "1"])
        .output()
        .unwrap();
    assert!(!run.status.success());
    assert!(String::from_utf8_lossy(&run.stderr).contains("budget"));
    assert!(!temp.0.join("Residues.lean").exists());
    assert_eq!(fs::read_to_string(&manifest).unwrap(), "prior result");
    let run = temp
        .command()
        .args(["--certificate", "out/residue_sieve_rust.json"])
        .output()
        .unwrap();
    assert!(!run.status.success());
    assert!(String::from_utf8_lossy(&run.stderr).contains("must differ"));
    assert_eq!(fs::read_to_string(&manifest).unwrap(), "prior result");
}

#[test]
#[ignore = "requires the pinned Lean 4.31.0 toolchain"]
fn generated_proofs_compile_for_empty_shallow_and_branched_coverage() {
    let temp = Output::new();
    for depth in ["0", "1", "8"] {
        let run = temp
            .command()
            .args(["--depth", depth, "--verify-lean"])
            .output()
            .unwrap();
        assert!(
            run.status.success(),
            "depth {depth}: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        let data: Value =
            serde_json::from_slice(&fs::read(temp.0.join("out/residue_sieve_rust.json")).unwrap())
                .unwrap();
        assert_eq!(data["certificate_status"], "verified");
        let log = fs::read_to_string(temp.0.join("out/residue_sieve_rust.log")).unwrap();
        assert!(!log.contains("sorryAx"));
    }
}

#[cfg(unix)]
#[test]
fn rejected_verification_is_recorded_as_failed() {
    use std::os::unix::fs::PermissionsExt;
    let temp = Output::new();
    let bin = temp.0.join("bin");
    fs::create_dir(&bin).unwrap();
    let lean = bin.join("lean");
    fs::write(
        &lean,
        "#!/bin/sh\necho 'simulated verifier rejection' >&2\nexit 1\n",
    )
    .unwrap();
    fs::set_permissions(&lean, fs::Permissions::from_mode(0o700)).unwrap();
    let paths = std::iter::once(bin).chain(
        std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()).collect::<Vec<_>>(),
    );
    let run = temp
        .command()
        .arg("--verify-lean")
        .env("PATH", std::env::join_paths(paths).unwrap())
        .output()
        .unwrap();
    assert!(!run.status.success());
    let data: Value =
        serde_json::from_slice(&fs::read(temp.0.join("out/residue_sieve_rust.json")).unwrap())
            .unwrap();
    assert_eq!(data["certificate_status"], "failed");
    let log = fs::read_to_string(temp.0.join("out/residue_sieve_rust.log")).unwrap();
    assert!(log.contains("simulated verifier rejection"));
}
