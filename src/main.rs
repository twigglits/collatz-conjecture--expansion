use collatz_search::{Row, Seed, certificates, pinned_lean_toolchain, search, seeds};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, path::PathBuf, process::Command, time::Instant};

const ROOT: &str = env!("CARGO_MANIFEST_DIR");

struct Options {
    fuel: u64,
    threads: usize,
    verify_lean: bool,
    bench: Option<usize>,
    output_dir: PathBuf,
    certificate: PathBuf,
}

fn options() -> Result<Option<Options>, String> {
    let mut opts = Options {
        fuel: 300_000,
        threads: 1,
        verify_lean: false,
        bench: None,
        output_dir: PathBuf::from(ROOT).join("results"),
        certificate: PathBuf::from(ROOT).join("CollatzSearchCertsRust.lean"),
    };
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--verify-lean" => opts.verify_lean = true,
            "--fuel" => {
                opts.fuel = args
                    .next()
                    .ok_or("--fuel needs a number")?
                    .parse()
                    .map_err(|_| "--fuel must be a nonnegative integer")?;
            }
            "--threads" => {
                opts.threads = args
                    .next()
                    .ok_or("--threads needs a number")?
                    .parse()
                    .map_err(|_| "--threads must be a positive integer")?;
                if opts.threads == 0 {
                    return Err("--threads must be positive".into());
                }
            }
            "--bench" => {
                let n = args
                    .next()
                    .ok_or("--bench needs a repetition count")?
                    .parse()
                    .map_err(|_| "--bench must be a positive integer")?;
                if n == 0 {
                    return Err("--bench must be positive".into());
                }
                opts.bench = Some(n);
            }
            "--output-dir" => {
                opts.output_dir = args.next().ok_or("--output-dir needs a path")?.into()
            }
            "--certificate" => {
                opts.certificate = args.next().ok_or("--certificate needs a path")?.into()
            }
            "--help" | "-h" => {
                println!(
                    "Exact positive-integer Collatz search (1,257 deterministic starts)\n\
                    Usage: collatz-search [--verify-lean] [--fuel N] [--threads N]\n\
                    [--output-dir DIR] [--certificate FILE] [--bench REPEATS]\n\n\
                    --fuel N          Ordinary steps per start (default 300000; timeout is unresolved)\n\
                    --threads N       Independent workers (default 1)\n\
                    --verify-lean     Independently verify successful trajectories with {}\n\
                    --bench REPEATS   Time search only; emit JSON, do not write artifacts or run Lean\n\
                    Default artifacts: results/counterexample_search_rust.json and\n\
                    CollatzSearchCertsRust.lean in the project directory.\n\
                    Use a release build for performance: cargo run --release -- --verify-lean",
                    pinned_lean_toolchain()
                );
                return Ok(None);
            }
            _ => return Err(format!("unknown argument {arg}; use --help")),
        }
    }
    if opts.bench.is_some() && opts.verify_lean {
        return Err("--bench measures search only; run --verify-lean separately".into());
    }
    let cwd = env::current_dir().map_err(|e| e.to_string())?;
    if opts.certificate.is_relative() {
        opts.certificate = cwd.join(opts.certificate);
    }
    if opts.output_dir.is_relative() {
        opts.output_dir = cwd.join(opts.output_dir);
    }
    Ok(Some(opts))
}

fn run_rows(inputs: &[Seed], fuel: u64, threads: usize) -> Result<Vec<Row>, String> {
    fn chunk(inputs: &[Seed], fuel: u64) -> Result<Vec<Row>, String> {
        inputs
            .iter()
            .map(|seed| {
                Ok(Row {
                    trace: search::trace(&seed.start, fuel)?,
                    seed: seed.clone(),
                })
            })
            .collect()
    }
    if threads == 1 || inputs.len() < 2 {
        return chunk(inputs, fuel);
    }
    std::thread::scope(|scope| {
        let handles: Vec<_> = inputs
            .chunks(inputs.len().div_ceil(threads.min(inputs.len())))
            .map(|part| {
                std::thread::Builder::new()
                    .spawn_scoped(scope, move || chunk(part, fuel))
                    .map_err(|e| format!("could not start a search worker: {e}"))
            })
            .collect::<Result<_, _>>()?;
        let mut result = Vec::with_capacity(inputs.len());
        for handle in handles {
            result.extend(handle.join().map_err(|_| "search worker panicked")??);
        }
        Ok(result)
    })
}

fn summary(rows: &[&Row]) -> Value {
    let mut counts = BTreeMap::<&str, usize>::new();
    for row in rows {
        *counts.entry(&row.trace.status).or_default() += 1;
    }
    let good: Vec<_> = rows
        .iter()
        .copied()
        .filter(|r| r.trace.status == "reached_one")
        .collect();
    // Preserve Python's first-item tie breaking instead of Iterator::max_by_key's last item.
    let longest = good.iter().fold(None::<&&Row>, |best, row| {
        if best.is_none_or(|b| row.trace.steps > b.trace.steps) {
            Some(row)
        } else {
            best
        }
    });
    let latest = good.iter().fold(None::<&&Row>, |best, row| {
        if best.is_none_or(|b| row.trace.first_descent > b.trace.first_descent) {
            Some(row)
        } else {
            best
        }
    });
    json!({
        "cases": rows.len(), "status_counts": counts,
        "min_start_bits": rows.iter().map(|r| r.seed.start.bits()).min().unwrap_or(0),
        "max_start_bits": rows.iter().map(|r| r.seed.start.bits()).max().unwrap_or(0),
        "certified_trajectory_metrics": {
            "cases": good.len(),
            "total_steps": good.iter().map(|r| u128::from(r.trace.steps)).sum::<u128>(),
            "max_steps": good.iter().map(|r| r.trace.steps).max().unwrap_or(0),
            "max_peak_bits": good.iter().map(|r| r.trace.peak_bits).max().unwrap_or(0),
            "max_first_descent": good.iter().map(|r| r.trace.first_descent).max().unwrap_or(0)
        },
        "longest_trajectory": longest.map(|r| &r.seed.label),
        "latest_first_descent": latest.map(|r| &r.seed.label)
    })
}

fn write_json(path: &std::path::Path, data: &Value) -> Result<(), Box<dyn std::error::Error>> {
    fs::write(path, format!("{}\n", serde_json::to_string_pretty(data)?))?;
    Ok(())
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let Some(opts) = options()? else {
        return Ok(());
    };
    let seed_clock = Instant::now();
    let inputs = seeds::seeds();
    let worker_count = inputs
        .len()
        .div_ceil(inputs.len().div_ceil(opts.threads.min(inputs.len())));
    let seed_seconds = seed_clock.elapsed().as_secs_f64();
    let mut times = Vec::new();
    let mut rows = Vec::new();
    for repeat in 0..opts.bench.unwrap_or(1) {
        let start = Instant::now();
        rows = run_rows(&inputs, opts.fuel, opts.threads)?;
        times.push(start.elapsed().as_secs_f64());
        if opts.bench.is_some() {
            eprintln!("Completed search repetition {}", repeat + 1);
        }
    }
    let all: Vec<_> = rows.iter().collect();
    let overall = summary(&all);
    let family_summaries: serde_json::Map<String, Value> = seeds::FAMILIES
        .iter()
        .map(|f| {
            (
                f.to_string(),
                summary(
                    &rows
                        .iter()
                        .filter(|r| r.seed.family == *f)
                        .collect::<Vec<_>>(),
                ),
            )
        })
        .collect();
    if opts.bench.is_some() {
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({
                "implementation": "Rust", "profile": if cfg!(debug_assertions) {"debug"} else {"release"},
            "threads": opts.threads, "worker_count": worker_count, "fuel_ordinary_steps": opts.fuel,
                "seed_generation_seconds": seed_seconds, "search_seconds": times,
                "summary": overall, "families": family_summaries,
                "scope": "search and row collection only; excludes seed generation, export, compilation, and Lean"
            }))?
        );
        return Ok(());
    }
    let export_clock = Instant::now();
    let source = certificates::generate_lean(&rows);
    fs::create_dir_all(&opts.output_dir)?;
    if let Some(parent) = opts
        .certificate
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
    {
        fs::create_dir_all(parent)?;
    }
    let resolve_output = |path: &std::path::Path| -> std::io::Result<PathBuf> {
        path.canonicalize().or_else(|_| {
            Ok(path
                .parent()
                .unwrap()
                .canonicalize()?
                .join(path.file_name().unwrap()))
        })
    };
    let output = opts.output_dir.join("counterexample_search_rust.json");
    let log_output = opts.output_dir.join("counterexample_search_rust.log");
    let resolved_cert = resolve_output(&opts.certificate)?;
    if resolved_cert == resolve_output(&output)? || resolved_cert == resolve_output(&log_output)? {
        return Err(
            "--certificate must differ from the JSON manifest and verification log paths".into(),
        );
    }
    fs::write(&opts.certificate, &source)?;
    let mut data = json!({
        "schema": 1, "implementation": "Rust", "threads": opts.threads, "worker_count": worker_count,
        "map": "odd n -> 3*n+1; even n -> n/2; positive integers",
        "fuel_ordinary_steps": opts.fuel, "integer_arithmetic": "arbitrary precision (num-bigint)",
        "coverage": "explicit structured and deterministic hash-derived starts only; not an interval",
        "certificate_status": "not_run",
        "certificate_trust": "native_decide / generated native axioms; Lean compiler and runtime",
        "certificate_file": opts.certificate,
        "certificate_sha256": format!("{:x}", Sha256::digest(source.as_bytes())),
        "summary": overall, "families": family_summaries, "rows": rows,
        "timings_seconds": {"seed_generation": seed_seconds, "search": times[0]}
    });
    write_json(&output, &data)?;
    data["timings_seconds"]["export"] = json!(export_clock.elapsed().as_secs_f64());
    if opts.verify_lean {
        let toolchain = pinned_lean_toolchain();
        let selector = format!("+{toolchain}");
        eprintln!("Replaying successful trajectories with {toolchain}...");
        let lean_clock = Instant::now();
        let version = Command::new("lean")
            .arg(&selector)
            .arg("--version")
            .output()?;
        if !version.status.success() {
            return Err(String::from_utf8_lossy(&version.stderr).into_owned().into());
        }
        let checked = Command::new("lean")
            .arg(&selector)
            .arg(&opts.certificate)
            .current_dir(ROOT)
            .output()?;
        let log = format!(
            "Command: lean {selector} {}\n{}{}{}",
            opts.certificate.display(),
            String::from_utf8_lossy(&version.stdout),
            String::from_utf8_lossy(&checked.stdout),
            String::from_utf8_lossy(&checked.stderr)
        );
        fs::write(opts.output_dir.join("counterexample_search_rust.log"), &log)?;
        data["certificate_status"] = json!(if checked.status.success() {
            "verified"
        } else {
            "failed"
        });
        data["lean_version"] = json!(String::from_utf8_lossy(&version.stdout).trim());
        data["timings_seconds"]["lean"] = json!(lean_clock.elapsed().as_secs_f64());
        write_json(&output, &data)?;
        if !checked.status.success() {
            return Err(format!("Lean rejected the certificate:\n{log}").into());
        }
    } else {
        write_json(&output, &data)?;
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "certificate_status": data["certificate_status"], "summary": data["summary"],
            "families": data["families"], "timings_seconds": data["timings_seconds"],
            "manifest": output
        }))?
    );
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}
