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
        stderr.contains("stopped by wall-clock crash-containment bound"),
        "{stderr}"
    );
    assert!(!stderr.contains("proof error"), "{stderr}");

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
