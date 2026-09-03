use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

use click::cli::{files_with_extension, read_verifying_sources, source_refs};
use click::instrumentation::{self, ContractFallback};
use click::surface::verify_c0_sources;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
const SOURCE_MANIFEST: &str = "SOURCE.sha256";
const SOURCE_METADATA: &str = "SOURCE.md";

/// Known-broken or pathologically slow projects, skipped by default so the
/// suite is a meaningful green gate. Run one with `CLICK_EXAMPLE=<name>`, or
/// all of them with `CLICK_RUN_QUARANTINED=1`. Each entry names the reason;
/// remove entries as they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[];

/// The body-rerun ratchet (`docs/internals/testing.md`) over every example
/// project; see `tests/mdtests.rs` for the rule.
const CONTRACT_FALLBACK_BASELINE: &[(ContractFallback, usize)] = &[];

#[test]
fn example_projects() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let examples_dir = manifest_dir.join("examples");
    let requested = std::env::var_os("CLICK_EXAMPLE");
    let run_quarantined = requested.is_some() || std::env::var_os(RUN_QUARANTINED).is_some();
    let mut projects = fs::read_dir(&examples_dir)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", examples_dir.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("failed to read examples directory entry: {error}"))
                .path()
        })
        .filter(|path| path.is_dir())
        .filter(|path| {
            requested.as_ref().is_none_or(|requested| {
                path.file_name()
                    .is_some_and(|name| name == requested.as_os_str())
            })
        })
        .collect::<Vec<_>>();
    projects.sort();

    if !run_quarantined {
        projects.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            let quarantine = name.and_then(|name| {
                QUARANTINED
                    .iter()
                    .find(|(quarantined, _)| *quarantined == name)
            });
            match quarantine {
                Some((name, reason)) => {
                    println!("SKIPPING quarantined example `{name}`: {reason}");
                    false
                }
                None => true,
            }
        });
        assert!(
            !projects.is_empty(),
            "every example project is quarantined; run them with {RUN_QUARANTINED}=1",
        );
    }

    assert!(
        !projects.is_empty(),
        "expected at least one matching example project in `{}`",
        examples_dir.display(),
    );

    // Keep project verification serial and fail fast. Deterministic tactic
    // work budgets decide correctness; the test runner owns hang containment.
    let _ = instrumentation::take_body_rerun_census();
    for project in &projects {
        // One line as each project starts and one as it finishes, on stderr
        // so the gate can stream them: a stall shows as a started project
        // that never finishes, and a slow project is visible while it runs.
        eprintln!("example project `{}` started", project.display());
        let started = std::time::Instant::now();
        if let Err(diagnostics) = run_example_in_thread(project) {
            panic!("example project `{}` {diagnostics}", project.display());
        }
        eprintln!(
            "example project `{}` verified in {:.2}s",
            project.display(),
            started.elapsed().as_secs_f64()
        );
    }
    let census = instrumentation::take_body_rerun_census();
    if requested.is_none()
        && !run_quarantined
        && let Some(mismatch) =
            instrumentation::body_rerun_census_mismatch(&census, CONTRACT_FALLBACK_BASELINE)
    {
        panic!("body rerun ratchet (tests/examples.rs baselines):\n{mismatch}");
    }
}

fn run_example_in_thread(project: &Path) -> Result<(), String> {
    let project = project.to_path_buf();
    std::thread::Builder::new()
        .name("click-example".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            instrumentation::without_tactic_time_limits(|| run_example_project(&project))
        })
        .map_err(|error| format!("failed to start example verifier: {error}"))?
        .join()
        .map_err(|_| "example verifier panicked".to_string())?
}

fn run_example_project(project: &Path) -> Result<(), String> {
    let source_status = verify_source_integrity(project)?;
    if let Some(status) = source_status {
        eprintln!(
            "source fixture `{}` integrity manifest passed; status: {}",
            project.display(),
            status.as_str()
        );
    }

    let mut click_paths = files_with_extension(project, "click")?;

    if click_paths.is_empty() {
        return Err(format!(
            "example project `{}` must contain at least one .click sidecar",
            project.display()
        ));
    }

    click_paths.sort();

    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
        let c_sources = read_verifying_sources(&click_path, &click_source)?;
        match source_status {
            Some(SourceFixtureStatus::ParserOnly) => {
                match verify_c0_sources(&click_source, &source_refs(&c_sources)) {
                    Err(error) if error.message().starts_with("failed to parse C source") => {
                        eprintln!(
                            "parser status for `{}`: parser-only as expected: {}",
                            click_path.display(),
                            error.message()
                        );
                    }
                    Err(error) => {
                        return Err(format!(
                            "sidecar `{}` reached verification despite parser-only status: {}",
                            click_path.display(),
                            error.message()
                        ));
                    }
                    Ok(_) => {
                        return Err(format!(
                            "parser-only source fixture `{}` unexpectedly verified",
                            click_path.display()
                        ));
                    }
                }
            }
            Some(SourceFixtureStatus::Verified) | None => {
                verify_c0_sources(&click_source, &source_refs(&c_sources)).map_err(|error| {
                    format!(
                        "sidecar `{}` failed: {}",
                        click_path.display(),
                        error.message()
                    )
                })?;
                eprintln!("verified {}", click_path.display());
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceFixtureStatus {
    ParserOnly,
    Verified,
}

impl SourceFixtureStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::ParserOnly => "parser-only",
            Self::Verified => "verified",
        }
    }
}

fn verify_source_integrity(project: &Path) -> Result<Option<SourceFixtureStatus>, String> {
    let manifest_path = project.join(SOURCE_MANIFEST);
    if !manifest_path.is_file() {
        return Ok(None);
    }

    let metadata_path = project.join(SOURCE_METADATA);
    let metadata = fs::read_to_string(&metadata_path).map_err(|error| {
        format!(
            "source integrity manifest requires `{}`: {error}",
            metadata_path.display()
        )
    })?;
    let status = metadata
        .lines()
        .find_map(|line| line.trim().strip_prefix("status:"))
        .map(str::trim)
        .ok_or_else(|| {
            format!(
                "`{}` must declare `status: verified` or `status: parser-only`",
                metadata_path.display()
            )
        })
        .and_then(|status| match status {
            "verified" => Ok(SourceFixtureStatus::Verified),
            "parser-only" => Ok(SourceFixtureStatus::ParserOnly),
            _ => Err(format!(
                "`{}` has unsupported source status `{status}`",
                metadata_path.display()
            )),
        })?;

    let manifest = fs::read_to_string(&manifest_path)
        .map_err(|error| format!("failed to read `{}`: {error}", manifest_path.display()))?;
    let mut expected = BTreeMap::new();
    for (line_number, line) in manifest.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut fields = line.split_whitespace();
        let digest = fields.next().ok_or_else(|| {
            format!(
                "`{}` line {} has no digest",
                manifest_path.display(),
                line_number + 1
            )
        })?;
        let name = fields.next().ok_or_else(|| {
            format!(
                "`{}` line {} has no source path",
                manifest_path.display(),
                line_number + 1
            )
        })?;
        if fields.next().is_some() {
            return Err(format!(
                "`{}` line {} must contain exactly a digest and path",
                manifest_path.display(),
                line_number + 1
            ));
        }
        if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!(
                "`{}` line {} has an invalid SHA-256 digest",
                manifest_path.display(),
                line_number + 1
            ));
        }
        let path = Path::new(name);
        if path.is_absolute()
            || path.components().any(|component| {
                matches!(
                    component,
                    Component::ParentDir | Component::RootDir | Component::Prefix(_)
                )
            })
            || path.extension().and_then(|extension| extension.to_str()) != Some("c")
        {
            return Err(format!(
                "`{}` line {} names an invalid C source path `{name}`",
                manifest_path.display(),
                line_number + 1
            ));
        }
        if expected
            .insert(name.to_string(), digest.to_ascii_lowercase())
            .is_some()
        {
            return Err(format!(
                "`{}` lists source `{name}` more than once",
                manifest_path.display()
            ));
        }
    }
    if expected.is_empty() {
        return Err(format!(
            "`{}` contains no source entries",
            manifest_path.display()
        ));
    }

    let actual_sources = files_with_extension(project, "c")?
        .into_iter()
        .map(|path| {
            path.strip_prefix(project)
                .map_err(|error| format!("failed to relativize `{}`: {error}", path.display()))
                .and_then(|path| {
                    path.to_str().map(str::to_owned).ok_or_else(|| {
                        format!("source path `{}` is not valid UTF-8", path.display())
                    })
                })
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    let expected_sources = expected.keys().cloned().collect::<BTreeSet<_>>();
    if actual_sources != expected_sources {
        return Err(format!(
            "`{}` must cover exactly the project C sources; expected {expected_sources:?}, found {actual_sources:?}",
            manifest_path.display()
        ));
    }

    for (name, expected_digest) in expected {
        let path = project.join(&name);
        let source = fs::read(&path)
            .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
        let actual_digest = hex_digest(sha256(&source));
        if actual_digest != expected_digest {
            return Err(format!(
                "source integrity mismatch for `{}`: manifest has `{expected_digest}`, file has `{actual_digest}`",
                path.display()
            ));
        }
    }
    Ok(Some(status))
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    const INITIAL: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const ROUND: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    let bit_length = (bytes.len() as u64)
        .checked_mul(8)
        .expect("SHA-256 input is too large");
    let padded_length = bytes
        .len()
        .checked_add(9)
        .expect("SHA-256 input is too large")
        .div_ceil(64)
        * 64;
    let mut padded = Vec::with_capacity(padded_length);
    padded.extend_from_slice(bytes);
    padded.push(0x80);
    padded.resize(padded_length - 8, 0);
    padded.extend_from_slice(&bit_length.to_be_bytes());

    let mut state = INITIAL;
    for chunk in padded.chunks_exact(64) {
        let mut schedule = [0u32; 64];
        for (index, word) in schedule[..16].iter_mut().enumerate() {
            let start = index * 4;
            *word = u32::from_be_bytes(chunk[start..start + 4].try_into().unwrap());
        }
        for index in 16..64 {
            let first = schedule[index - 15].rotate_right(7)
                ^ schedule[index - 15].rotate_right(18)
                ^ (schedule[index - 15] >> 3);
            let second = schedule[index - 2].rotate_right(17)
                ^ schedule[index - 2].rotate_right(19)
                ^ (schedule[index - 2] >> 10);
            schedule[index] = schedule[index - 16]
                .wrapping_add(first)
                .wrapping_add(schedule[index - 7])
                .wrapping_add(second);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..64 {
            let choice = (e & f) ^ ((!e) & g);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let first = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let second = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let temporary_1 = h
                .wrapping_add(first)
                .wrapping_add(choice)
                .wrapping_add(ROUND[index])
                .wrapping_add(schedule[index]);
            let temporary_2 = second.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temporary_1);
            d = c;
            c = b;
            b = a;
            a = temporary_1.wrapping_add(temporary_2);
        }
        for (slot, value) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *slot = slot.wrapping_add(value);
        }
    }

    let mut digest = [0u8; 32];
    for (index, word) in state.iter().enumerate() {
        digest[index * 4..index * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    digest
}

fn hex_digest(digest: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    digest
        .into_iter()
        .flat_map(|byte| {
            [
                HEX[(byte >> 4) as usize] as char,
                HEX[(byte & 0x0f) as usize] as char,
            ]
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_matches_known_vector() {
        assert_eq!(
            hex_digest(sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn source_manifest_rejects_modified_file() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after the Unix epoch")
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "click-source-integrity-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir(&directory).expect("temporary source directory should be creatable");
        fs::write(directory.join(SOURCE_METADATA), "status: verified\n").unwrap();
        let source = b"int32 unchanged(void) { return 0; }\n";
        fs::write(directory.join("fixture.c"), source).unwrap();
        fs::write(
            directory.join(SOURCE_MANIFEST),
            format!("{}  fixture.c\n", hex_digest(sha256(source))),
        )
        .unwrap();

        assert_eq!(
            verify_source_integrity(&directory).unwrap(),
            Some(SourceFixtureStatus::Verified)
        );
        fs::write(
            directory.join("fixture.c"),
            b"int32 changed(void) { return 1; }\n",
        )
        .unwrap();
        let error = verify_source_integrity(&directory).unwrap_err();
        assert!(error.contains("source integrity mismatch"), "{error}");
        fs::remove_dir_all(directory).unwrap();
    }
}
