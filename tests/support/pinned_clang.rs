//! The pinned LLVM 19.1.7 toolchain that hermetic C++ fixtures compile with.

use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

pub fn output(program: &Path, args: &[&str]) -> String {
    let result = Command::new(program).args(args).output().unwrap();
    assert!(
        result.status.success(),
        "{} {:?} failed: {}",
        program.display(),
        args,
        String::from_utf8_lossy(&result.stderr)
    );
    String::from_utf8(result.stdout).unwrap().trim().to_owned()
}

pub fn pinned_clang() -> PathBuf {
    let llvm_config = std::env::var_os("LLVM_CONFIG")
        .map(PathBuf::from)
        .or_else(|| {
            [
                "/usr/bin/llvm-config-19",
                "/usr/lib/llvm-19/bin/llvm-config",
                "/opt/homebrew/opt/llvm@19/bin/llvm-config",
            ]
            .into_iter()
            .map(PathBuf::from)
            .find(|path| path.is_file())
        })
        .expect("scripts/check.sh requires LLVM 19.1.7");
    assert_eq!(output(&llvm_config, &["--version"]), "19.1.7");
    let clang = std::env::var_os("CLANGXX")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(output(&llvm_config, &["--bindir"])).join("clang++"));
    assert!(
        output(&clang, &["--version"])
            .lines()
            .next()
            .unwrap_or_default()
            .contains("19.1.7")
    );
    clang
}
