//! Owned, bounded execution of the external preprocessing dependency.
//!
//! This module never interprets command strings. Every exit, including a
//! successful compiler exit with a surviving descendant, cleans up the owned
//! process group before returning.

use std::collections::BTreeMap;
use std::io::{self, Read};
use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug)]
pub(super) struct CompilerLimits {
    pub timeout: Duration,
    pub max_stdout_bytes: usize,
    pub max_stderr_bytes: usize,
}

#[derive(Debug)]
pub(super) struct CompilerOutput {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

pub(super) fn run_compiler(
    executable: &Path,
    arguments: &[String],
    cwd: &Path,
    environment: &BTreeMap<String, String>,
    limits: CompilerLimits,
) -> Result<CompilerOutput, String> {
    run_compiler_cancellable(executable, arguments, cwd, environment, limits, || {
        crate::instrumentation::deadline_exceeded()
    })
}

#[cfg(unix)]
fn run_compiler_cancellable(
    executable: &Path,
    arguments: &[String],
    cwd: &Path,
    environment: &BTreeMap<String, String>,
    limits: CompilerLimits,
    cancelled: impl Fn() -> bool,
) -> Result<CompilerOutput, String> {
    use std::os::unix::process::CommandExt;

    if limits.timeout.is_zero() || cancelled() {
        return Err("compiler invocation cancelled before launch".into());
    }
    let started = Instant::now();
    let child = Command::new(executable)
        .args(arguments)
        .current_dir(cwd)
        .env_clear()
        .envs(environment)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0)
        .spawn()
        .map_err(|error| format!("cannot start compiler `{}`: {error}", executable.display()))?;
    let mut group = OwnedCompilerGroup(child);
    let mut stdout = group.0.stdout.take().expect("compiler stdout was piped");
    let mut stderr = group.0.stderr.take().expect("compiler stderr was piped");
    nonblocking(&stdout)?;
    nonblocking(&stderr)?;
    let mut output = CompilerOutput {
        stdout: Vec::new(),
        stderr: Vec::new(),
    };
    let mut stdout_closed = false;
    let mut stderr_closed = false;
    let mut status = None;
    loop {
        if cancelled() {
            return Err("compiler invocation cancelled; its process group was stopped".into());
        }
        if started.elapsed() >= limits.timeout {
            return Err(format!(
                "compiler exceeded its {:?} deadline; its process group was stopped",
                limits.timeout
            ));
        }
        // A bounded drain per iteration prevents a busy stream from starving
        // cancellation, the other stream, or the process-exit check.
        if !stdout_closed {
            stdout_closed = drain(
                &mut stdout,
                &mut output.stdout,
                limits.max_stdout_bytes,
                "stdout",
            )?;
        }
        if !stderr_closed {
            stderr_closed = drain(
                &mut stderr,
                &mut output.stderr,
                limits.max_stderr_bytes,
                "stderr",
            )?;
        }
        if status.is_none() {
            status = group
                .0
                .try_wait()
                .map_err(|error| format!("cannot wait for compiler: {error}"))?;
            if status.is_some() {
                // A compiler that exits cannot delegate work beyond its
                // lifetime. Kill surviving children, then drain closed pipes.
                group.kill_descendants();
            }
        }
        if let Some(status) = status
            && stdout_closed
            && stderr_closed
        {
            if status.success() {
                return Ok(output);
            }
            let diagnostic = String::from_utf8_lossy(&output.stderr);
            let diagnostic = diagnostic.chars().take(2_000).collect::<String>();
            return Err(format!(
                "compiler exited with {status}: {}",
                diagnostic.trim()
            ));
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

#[cfg(unix)]
struct OwnedCompilerGroup(Child);

#[cfg(unix)]
impl OwnedCompilerGroup {
    fn kill_descendants(&self) {
        // process_group(0) gave this child its own group. The negative PID
        // addresses only that owned group, never the caller's group.
        unsafe {
            libc::kill(-(self.0.id() as libc::pid_t), libc::SIGKILL);
        }
    }
}

#[cfg(unix)]
impl Drop for OwnedCompilerGroup {
    fn drop(&mut self) {
        self.kill_descendants();
        // Reap the direct child even on output-limit, cancellation, setup, or
        // read errors. There are no detached reader threads or open pipe waits.
        let _ = self.0.wait();
    }
}

#[cfg(unix)]
fn nonblocking(stream: &impl std::os::fd::AsRawFd) -> Result<(), String> {
    let fd = stream.as_raw_fd();
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(format!(
            "cannot configure compiler output: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn drain(
    stream: &mut impl Read,
    output: &mut Vec<u8>,
    limit: usize,
    name: &str,
) -> Result<bool, String> {
    let mut buffer = [0_u8; 8192];
    for _ in 0..8 {
        match stream.read(&mut buffer) {
            Ok(0) => return Ok(true),
            Ok(count) => {
                if count > limit.saturating_sub(output.len()) {
                    return Err(format!(
                        "compiler {name} exceeded its {limit}-byte output limit"
                    ));
                }
                output.extend_from_slice(&buffer[..count]);
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(false),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(format!("cannot read compiler {name}: {error}")),
        }
    }
    Ok(false)
}

#[cfg(not(unix))]
fn run_compiler_cancellable(
    _executable: &Path,
    _arguments: &[String],
    _cwd: &Path,
    _environment: &BTreeMap<String, String>,
    _limits: CompilerLimits,
    _cancelled: impl Fn() -> bool,
) -> Result<CompilerOutput, String> {
    Err("compiler-backed imports currently require Unix process-group isolation".into())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn limits() -> CompilerLimits {
        CompilerLimits {
            timeout: Duration::from_secs(2),
            max_stdout_bytes: 100_000,
            max_stderr_bytes: 100_000,
        }
    }

    fn shell(script: &str, limits: CompilerLimits) -> Result<CompilerOutput, String> {
        run_compiler(
            Path::new("/bin/sh"),
            &["-c".into(), script.into()],
            Path::new("/tmp"),
            &BTreeMap::new(),
            limits,
        )
    }

    #[test]
    fn compiler_process_drains_both_streams_and_preserves_argument_bytes() {
        let output = run_compiler(
            Path::new("/bin/sh"),
            &[
                "-c".into(),
                "printf '%s' \"$1\"; printf diagnostic >&2".into(),
                "test".into(),
                "$(never_execute); `never_execute` * spaced".into(),
            ],
            Path::new("/tmp"),
            &BTreeMap::new(),
            limits(),
        )
        .unwrap();
        assert_eq!(output.stdout, b"$(never_execute); `never_execute` * spaced");
        assert_eq!(output.stderr, b"diagnostic");
        let output = shell(
            "i=0; while [ $i -lt 3000 ]; do printf out; printf err >&2; i=$((i+1)); done",
            limits(),
        )
        .unwrap();
        assert_eq!(output.stdout.len(), 9_000);
        assert_eq!(output.stderr.len(), 9_000);
    }

    #[test]
    fn compiler_process_rejects_partial_output_on_failure_and_limits() {
        assert!(
            shell("printf partial; printf bad >&2; exit 7", limits())
                .unwrap_err()
                .contains("bad")
        );
        for (script, stream) in [
            ("while :; do printf xxxxxxxxxx; done", "stdout"),
            ("while :; do printf xxxxxxxxxx >&2; done", "stderr"),
        ] {
            let error = shell(
                script,
                CompilerLimits {
                    max_stdout_bytes: 9,
                    max_stderr_bytes: 9,
                    ..limits()
                },
            )
            .unwrap_err();
            assert!(error.contains(stream), "{error}");
            assert!(error.contains("output limit"), "{error}");
        }
    }

    #[test]
    fn compiler_process_bounds_descendants_holding_pipes_and_cancellation() {
        let started = Instant::now();
        let result = shell(
            "sleep 30 & wait",
            CompilerLimits {
                timeout: Duration::from_millis(50),
                ..limits()
            },
        );
        assert!(result.unwrap_err().contains("deadline"));
        assert!(started.elapsed() < Duration::from_secs(2));
        // Even a successful parent may leave a pipe-owning child behind.
        assert!(shell("sleep 30 & exit 0", limits()).is_ok());
        let started = Instant::now();
        let error = run_compiler_cancellable(
            Path::new("/bin/sh"),
            &["-c".into(), "sleep 30 & wait".into()],
            Path::new("/tmp"),
            &BTreeMap::new(),
            limits(),
            || started.elapsed() >= Duration::from_millis(30),
        )
        .unwrap_err();
        assert!(error.contains("cancelled"));
        assert!(started.elapsed() < Duration::from_secs(2));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn compiler_process_timeout_leaves_no_running_worker() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "click-compiler-worker-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let error = run_compiler(
            Path::new("/bin/sh"),
            &[
                "-c".into(),
                "sleep 30 & printf '%s' \"$!\" > \"$1\"; wait".into(),
                "test".into(),
                path.to_str().unwrap().into(),
            ],
            Path::new("/tmp"),
            &BTreeMap::new(),
            CompilerLimits {
                timeout: Duration::from_millis(150),
                ..limits()
            },
        )
        .unwrap_err();
        assert!(error.contains("deadline"), "{error}");
        let pid = std::fs::read_to_string(&path).expect("child worker PID recorded");
        std::fs::remove_file(path).unwrap();
        let pid = pid.parse::<u32>().unwrap();
        // An orphan may briefly await the namespace init's reap, but it must
        // have exited: a zombie cannot run or retain compiler output pipes.
        for attempt in 0..50 {
            match std::fs::read_to_string(format!("/proc/{pid}/stat")) {
                Err(error) if error.kind() == io::ErrorKind::NotFound => return,
                Ok(stat)
                    if stat
                        .rsplit_once(") ")
                        .is_some_and(|(_, rest)| rest.starts_with('Z')) =>
                {
                    return;
                }
                state if attempt == 49 => panic!("compiler worker {pid} still running: {state:?}"),
                _ => std::thread::sleep(Duration::from_millis(2)),
            }
        }
    }
}
