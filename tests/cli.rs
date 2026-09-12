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

    #[cfg(unix)]
    {
        let alias = output.0.join("ManifestAlias.lean");
        fs::hard_link(output.0.join("out/counterexample_search_rust.json"), &alias).unwrap();
        let bad = output
            .command()
            .args(["--fuel", "0", "--certificate", "ManifestAlias.lean"])
            .output()
            .unwrap();
        assert!(!bad.status.success());
        assert!(String::from_utf8_lossy(&bad.stderr).contains("must differ"));
        assert_eq!(output.manifest(), original);
    }
}

#[cfg(unix)]
#[test]
fn lean_verification_checks_process_output_and_exit_status() {
    use std::os::unix::fs::PermissionsExt;

    for (message, code, expected) in [
        ("simulated verifier rejection", "1", "failed"),
        ("test_theorem depends on axioms: [sorryAx]", "0", "failed"),
        ("warning: declaration uses 'sorry'", "0", "failed"),
        ("verification passed", "0", "verified"),
    ] {
        let output = TempDir::new();
        let bin = output.0.join("bin");
        fs::create_dir(&bin).unwrap();
        let lean = bin.join("lean");
        fs::write(
            &lean,
            "#!/bin/sh\nif [ \"$2\" = --version ]; then\n  echo 'Lean test double'\n  exit 0\nfi\nprintf 'Selected toolchain: %s\\n' \"$1\"\nprintf '%s\\n' \"$COLLATZ_TEST_LEAN_MESSAGE\" >&2\nexit \"$COLLATZ_TEST_LEAN_EXIT\"\n",
        )
        .unwrap();
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o700)).unwrap();
        let paths = std::iter::once(bin).chain(
            std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
                .collect::<Vec<_>>(),
        );
        let run = output
            .command()
            .args([
                "--fuel",
                "0",
                "--verify-lean",
                "--certificate",
                "no-sorryAx.lean",
            ])
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("COLLATZ_TEST_LEAN_MESSAGE", message)
            .env("COLLATZ_TEST_LEAN_EXIT", code)
            .output()
            .unwrap();
        assert_eq!(run.status.success(), expected == "verified", "{message}");
        assert_eq!(output.manifest()["certificate_status"], expected);
        let log = fs::read_to_string(output.0.join("out/counterexample_search_rust.log")).unwrap();
        assert!(log.contains(message));
        assert!(log.contains(&format!(
            "Selected toolchain: +{}\n",
            collatz_search::pinned_lean_toolchain()
        )));
    }
}

#[test]
fn analysis_verifier_output_collisions_preserve_input() {
    let cases = [
        (
            env!("CARGO_BIN_EXE_analyze"),
            "--raw",
            "CollatzCerts.lean",
            false,
        ),
        (env!("CARGO_BIN_EXE_analyze"), "--raw", "summary.md", false),
        (
            env!("CARGO_BIN_EXE_analyze"),
            "--raw",
            "analysis.json",
            false,
        ),
        (env!("CARGO_BIN_EXE_analyze"), "--raw", "lean.log", true),
        (
            env!("CARGO_BIN_EXE_verify-frontier"),
            "--input",
            "frontier_summary_rust.md",
            false,
        ),
        (
            env!("CARGO_BIN_EXE_verify-frontier"),
            "--input",
            "frontier_verification_rust.json",
            false,
        ),
    ];
    let raw = include_str!("../results/raw.jsonl");
    for (program, input_option, name, verify_lean) in cases {
        let output = TempDir::new();
        let input = output.0.join(name);
        fs::write(&input, raw).unwrap();
        let mut command = Command::new(program);
        command
            .current_dir(&output.0)
            .args([input_option, name, "--output-dir", "."]);
        if verify_lean {
            command.arg("--verify-lean");
        }
        let run = command.output().unwrap();
        assert!(
            !run.status.success(),
            "accepted output collision for {name}"
        );
        assert!(String::from_utf8_lossy(&run.stderr).contains("must not overwrite input"));
        assert_eq!(fs::read_to_string(input).unwrap(), raw);
    }
}

#[cfg(unix)]
#[test]
fn verifiers_preserve_inputs_when_outputs_are_link_aliases() {
    let cases = [
        (
            env!("CARGO_BIN_EXE_analyze"),
            "--raw",
            "--output-dir",
            ".",
            "summary.md",
            include_str!("../results/raw.jsonl"),
        ),
        (
            env!("CARGO_BIN_EXE_verify-frontier"),
            "--input",
            "--output-dir",
            ".",
            "frontier_verification_rust.json",
            include_str!("../results/raw.jsonl"),
        ),
        (
            env!("CARGO_BIN_EXE_verify-universal"),
            "--input",
            "--output",
            "summary.md",
            "summary.md",
            include_str!("../results/universal.jsonl"),
        ),
    ];
    for (program, input_option, output_option, output_value, output_name, raw) in cases {
        for symbolic in [false, true] {
            let output = TempDir::new();
            let input = output.0.join("input.jsonl");
            let alias = output.0.join(output_name);
            fs::write(&input, raw).unwrap();
            if symbolic {
                std::os::unix::fs::symlink(&input, &alias).unwrap();
            } else {
                fs::hard_link(&input, &alias).unwrap();
            }
            let run = Command::new(program)
                .current_dir(&output.0)
                .args([input_option, "input.jsonl", output_option, output_value])
                .output()
                .unwrap();
            assert!(
                !run.status.success(),
                "accepted aliased output for {program}"
            );
            assert!(String::from_utf8_lossy(&run.stderr).contains("must not overwrite input"));
            assert_eq!(fs::read_to_string(&input).unwrap(), raw);
            assert_eq!(fs::read_to_string(&alias).unwrap(), raw);
        }
    }
}
