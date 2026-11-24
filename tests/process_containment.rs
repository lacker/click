#![cfg(debug_assertions)]

use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

// This is a containment regression, not a wall-clock proof verdict. The
// independent outer bound prevents a broken watchdog from hanging the gate.
const CONTAINMENT_TEST_OUTER_BOUND: Duration = Duration::from_secs(15);

fn bounded_output(mut command: Command) -> Output {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    loop {
        if child.try_wait().unwrap().is_some() {
            return child.wait_with_output().unwrap();
        }
        if started.elapsed() >= CONTAINMENT_TEST_OUTER_BOUND {
            child.kill().unwrap();
            let output = child.wait_with_output().unwrap();
            panic!(
                "CLI did not finish within the test containment bound: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn cli_watchdog_stops_a_verifier_that_does_not_poll() {
    let directory = tempfile::tempdir().unwrap();
    std::fs::write(directory.path().join("f.c"), "int f(void) { return 0; }\n").unwrap();
    std::fs::write(
        directory.path().join("f.click"),
        "verifying \"f.c\"; int32 f() { ensures result == 0; }\n",
    )
    .unwrap();

    let mut blocked = Command::new(env!("CARGO_BIN_EXE_click"));
    blocked
        .current_dir(directory.path())
        .args(["verify", "--time-limit", "1s", "f.click"])
        .env("CLICK_DEBUG_BLOCK_VERIFIER", "1");
    let output = bounded_output(blocked);
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("timed out:")
            && stderr.contains("stopped by wall-clock crash-containment bound"),
        "{stderr}"
    );
    assert!(!stderr.contains("unsuccessful search"), "{stderr}");

    // A successful operation cancels a long-lived watchdog rather than
    // waiting for it or allowing it to terminate a completed verification.
    let mut normal = Command::new(env!("CARGO_BIN_EXE_click"));
    normal
        .current_dir(directory.path())
        .args(["verify", "--time-limit", "5m", "f.click"])
        .env_remove("CLICK_DEBUG_BLOCK_VERIFIER");
    let output = bounded_output(normal);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn audit_run_deadline_prints_summary_and_resume() {
    let directory = tempfile::tempdir().unwrap();
    let source = (0..5000)
        .map(|index| format!("theorem identity_{index}() {{ ensures 0 == 0 by close(); }}\n"))
        .collect::<String>();
    std::fs::write(directory.path().join("unit.click"), source).unwrap();

    for cursor in [None, Some("unit.click:1:1")] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_click"));
        command.current_dir(directory.path()).args([
            "audit",
            "--time-limit",
            "1ms",
            "--session-time-limit",
            "5s",
        ]);
        command.env_remove("CLICK_DEBUG_BLOCK_VERIFIER");
        if let Some(cursor) = cursor {
            command.args(["--start-at", cursor]);
        }
        command.arg("unit.click");
        let output = bounded_output(command);
        assert_eq!(output.status.code(), Some(1));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stdout.contains("SUMMARY:"), "{stdout}\n{stderr}");
        assert!(stdout.contains("RESUME:"), "{stdout}\n{stderr}");
        if let Some(cursor) = cursor {
            assert!(stdout.contains(&format!("--start-at {cursor}")), "{stdout}");
        } else {
            assert!(!stdout.contains("--start-at"), "{stdout}");
        }
        assert!(stderr.contains("audit stopped at its"), "{stderr}");
        assert!(
            !stderr.contains("stopped by wall-clock crash-containment bound"),
            "{stderr}"
        );
    }
}

#[test]
fn audit_watchdog_keeps_its_configured_phase_bound() {
    let directory = tempfile::tempdir().unwrap();
    std::fs::write(
        directory.path().join("unit.click"),
        "theorem identity() { ensures 0 == 0 by close(); }\n",
    )
    .unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_click"));
    command
        .current_dir(directory.path())
        .args([
            "audit",
            "--time-limit",
            "1s",
            "--session-time-limit",
            "2s",
            "unit.click",
        ])
        .env("CLICK_DEBUG_BLOCK_VERIFIER", "1");
    let output = bounded_output(command);
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("stopped by wall-clock crash-containment bound after 2.000s"),
        "{stderr}"
    );
}
