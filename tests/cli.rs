use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_click")
}

fn temp_file(name: &str, contents: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time should move forward")
        .as_nanos();
    let path = env::temp_dir().join(format!("click-{name}-{unique}.cl"));
    fs::write(&path, contents).expect("temp file should be written");
    path
}

#[test]
fn evaluates_expression_argument() {
    let output = Command::new(bin())
        .args(["-e", "(app (lambda x (var x)) (record))"])
        .output()
        .expect("command should run");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout), "(record)\n");
}

#[test]
fn evaluates_file_and_ignores_shebang() {
    let path = temp_file(
        "shebang",
        "#!/usr/bin/env click\n(record (answer (record)))\n",
    );

    let output = Command::new(bin())
        .arg(&path)
        .output()
        .expect("command should run");

    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "(record (answer (record)))\n"
    );

    fs::remove_file(path).expect("temp file should be removed");
}

#[test]
fn evaluates_stdin() {
    let mut child = Command::new(bin())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("command should spawn");

    {
        use std::io::Write;

        let stdin = child.stdin.as_mut().expect("stdin should be available");
        write!(
            stdin,
            "(app (lambda x (record (answer (var x)))) (record))\n"
        )
        .expect("stdin write should succeed");
    }

    let output = child.wait_with_output().expect("command should complete");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "(record (answer (record)))\n"
    );
}
