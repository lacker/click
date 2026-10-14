//! The pinned Linux `lib/rbtree.c` input closure in
//! `integrations/linux-rbtree/`.
//!
//! The committed import lock and artifact load offline, and with the
//! recorded GCC the lock is reproduced. No proof runs against the imported
//! bodies yet; the tests pin the frontier so that progress and regressions
//! both show up as a changed expectation.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use sha2::{Digest, Sha256};

use super::compiler_import::{create_lock, load_imports};
use super::{provenance::CSourceMap, syntax};
use crate::source::SourcePosition;

/// The first rejection of the complete pinned translation unit: the
/// anonymous union member of `struct ftrace_branch_data`, the artifact's
/// first declaration.
const FIRST_REJECTION: &str =
    "././include/linux/compiler_types.h:172: expected union name, got `{`";

/// The functions the dependency-closure projection of the pinned unit
/// defines: every function in `lib/rbtree.c` and every inline helper they
/// reach, by kernel identity.
const PROJECTED_FUNCTIONS: &[&str] = &[
    "____rb_erase_color#inline:lib/rbtree.c",
    "__rb_change_child#inline:lib/rbtree.c",
    "__rb_change_child_rcu#inline:lib/rbtree.c",
    "__rb_erase_augmented#inline:lib/rbtree.c",
    "__rb_erase_color",
    "__rb_insert#inline:lib/rbtree.c",
    "__rb_insert_augmented",
    "__rb_rotate_set_parents#inline:lib/rbtree.c",
    "dummy_copy#inline:lib/rbtree.c",
    "dummy_propagate#inline:lib/rbtree.c",
    "dummy_rotate#inline:lib/rbtree.c",
    "rb_erase",
    "rb_first",
    "rb_first_postorder",
    "rb_insert_color",
    "rb_last",
    "rb_left_deepest_node#inline:lib/rbtree.c",
    "rb_next",
    "rb_next_postorder",
    "rb_prev",
    "rb_red_parent#inline:lib/rbtree.c",
    "rb_replace_node",
    "rb_replace_node_rcu",
    "rb_set_black#inline:lib/rbtree.c",
    "rb_set_parent#inline:lib/rbtree.c",
    "rb_set_parent_color#inline:lib/rbtree.c",
];

/// File-scope items the projection keeps and omits.
const PROJECTED_ITEMS: (usize, usize) = (32, 2543);

/// Set to a non-empty value to fail, instead of reporting, when the host
/// toolchain is not the recorded one.
const REQUIRE_TOOLCHAIN: &str = "CLICK_LINUX_RBTREE_REQUIRE_TOOLCHAIN";

/// Set to an output path to write the per-declaration rejection inventory.
const INVENTORY: &str = "CLICK_LINUX_RBTREE_INVENTORY";

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("integrations/linux-rbtree")
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn provenance() -> serde_json::Value {
    serde_json::from_slice(&fs::read(fixture().join("provenance.json")).unwrap()).unwrap()
}

fn text<'a>(value: &'a serde_json::Value, path: &[&str]) -> &'a str {
    path.iter()
        .fold(value, |value, key| &value[*key])
        .as_str()
        .unwrap_or_else(|| panic!("provenance has no string at {path:?}"))
}

/// The closure extracted into a fresh directory, removed on drop.
struct Closure(PathBuf);

impl Drop for Closure {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Extracts the checked-in archive after checking it, member by member,
/// against the provenance record.
fn extract_closure(provenance: &serde_json::Value) -> Closure {
    let archive = fs::read(fixture().join("input-closure.tar.gz")).unwrap();
    extract_archive(provenance, &archive, true)
}

/// `check_archive_hash` is false only for the tamper regressions, which
/// reach the per-member checks behind the whole-archive hash.
fn extract_archive(
    provenance: &serde_json::Value,
    archive: &[u8],
    check_archive_hash: bool,
) -> Closure {
    if check_archive_hash {
        assert_eq!(
            sha256(archive),
            text(provenance, &["closure", "archive_sha256"]),
            "input-closure.tar.gz differs from provenance.json"
        );
    }
    let mut expected = provenance["closure"]["files"]
        .as_array()
        .unwrap()
        .iter()
        .map(|file| {
            (
                file["path"].as_str().unwrap().to_string(),
                (
                    file["sha256"].as_str().unwrap().to_string(),
                    file["bytes"].as_u64().unwrap(),
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let notices = provenance["closure"]["notices"]
        .as_array()
        .unwrap()
        .iter()
        .map(|notice| notice.as_str().unwrap())
        .collect::<Vec<_>>();

    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let root = std::env::temp_dir().join(format!(
        "click-linux-rbtree-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).expect("create isolated closure directory");
    let closure = Closure(root);
    let mut entries = tar::Archive::new(flate2::read::GzDecoder::new(archive));
    for entry in entries.entries().unwrap() {
        let mut entry = entry.unwrap();
        assert!(
            entry.header().entry_type().is_file(),
            "the closure holds only regular files"
        );
        let path = entry.path().unwrap().to_str().unwrap().to_string();
        let mut bytes = Vec::new();
        entry.read_to_end(&mut bytes).unwrap();
        match expected.remove(&path) {
            Some((digest, size)) => {
                assert_eq!(bytes.len() as u64, size, "{path}: size differs");
                assert_eq!(sha256(&bytes), digest, "{path}: content differs");
            }
            None => assert!(
                notices.contains(&path.as_str()),
                "{path}: not a recorded input"
            ),
        }
        assert!(
            Path::new(&path)
                .components()
                .all(|part| matches!(part, std::path::Component::Normal(_))),
            "{path}: not a plain relative path"
        );
        let target = closure.0.join(&path);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::write(target, bytes).unwrap();
    }
    assert!(
        expected.is_empty(),
        "recorded inputs missing from the closure: {:?}",
        expected.keys().collect::<Vec<_>>()
    );
    closure
}

/// A project laid out as the committed import expects: the checked closure
/// extracted into `inputs/`, beside the named fixture files.
fn import_layout(provenance: &serde_json::Value, files: &[&str]) -> Closure {
    let extracted = extract_closure(provenance);
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let root = fs::canonicalize(std::env::temp_dir())
        .unwrap()
        .join(format!(
            "click-linux-rbtree-import-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
    fs::create_dir(&root).expect("create isolated import directory");
    let layout = Closure(root);
    fs::rename(&extracted.0, layout.0.join("inputs")).expect("move the closure into inputs/");
    for name in files {
        fs::copy(fixture().join(name), layout.0.join(name)).unwrap();
    }
    layout
}

fn read_lock(path: &Path) -> serde_json::Value {
    serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
}

/// Whether the host compiler driver and `cc1` are the recorded binaries.
fn recorded_toolchain(provenance: &serde_json::Value) -> Result<(), String> {
    for tool in ["gcc", "cc1"] {
        let path = text(provenance, &["toolchain", tool, "path"]);
        let bytes = fs::read(path).map_err(|error| format!("{path}: {error}"))?;
        if sha256(&bytes) != text(provenance, &["toolchain", tool, "sha256"]) {
            return Err(format!("{path} is not the recorded binary"));
        }
    }
    Ok(())
}

/// `Ok(None)` when the host has the recorded compiler. Otherwise the
/// frontier checks cannot run: that is a notice to print, or an error when
/// the recorded compiler is required.
fn toolchain_gate(
    provenance: &serde_json::Value,
    required: bool,
) -> Result<Option<String>, String> {
    match recorded_toolchain(provenance) {
        Ok(()) => Ok(None),
        Err(reason) if required => Err(format!("{REQUIRE_TOOLCHAIN} is set, but {reason}")),
        Err(reason) => Ok(Some(format!(
            "linux-rbtree: NOT CHECKED: locking and preprocessing need the recorded GCC ({reason}); only the closure was checked"
        ))),
    }
}

#[test]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn linux_rbtree_gate_reports_or_refuses_another_compiler() {
    // Another compiler is simulated by recording a different identity.
    let mut other_binary = provenance();
    other_binary["toolchain"]["cc1"]["sha256"] = "0".repeat(64).into();
    let mut missing = provenance();
    missing["toolchain"]["gcc"]["path"] = "/nonexistent/click-linux-rbtree-gcc".into();
    for (provenance, reason) in [
        (other_binary, "is not the recorded binary"),
        (missing, "/nonexistent/click-linux-rbtree-gcc"),
    ] {
        // The reason does not depend on whether this host has the recorded
        // compiler: an unreadable recorded `gcc` path is also "another compiler".
        let Err(actual) = recorded_toolchain(&provenance) else {
            panic!("a changed identity must not match the host compiler");
        };
        if fs::metadata(text(&provenance, &["toolchain", "gcc", "path"])).is_ok()
            && fs::metadata(text(&provenance, &["toolchain", "cc1", "path"])).is_ok()
        {
            assert!(actual.contains(reason), "{actual}");
        }
        let notice = toolchain_gate(&provenance, false)
            .expect("another compiler is not a failure by default")
            .expect("another compiler must be reported, not silently accepted");
        assert!(notice.contains("NOT CHECKED"), "{notice}");
        let refusal = toolchain_gate(&provenance, true)
            .expect_err("a required recorded compiler must fail the gate");
        assert!(refusal.contains(REQUIRE_TOOLCHAIN), "{refusal}");
    }
}

fn panic_message(result: std::thread::Result<Closure>) -> String {
    let payload = result.err().expect("a tampered closure must be refused");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|text| text.to_string()))
        .unwrap_or_default()
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn linux_rbtree_gate_refuses_a_tampered_closure() {
    let provenance = provenance();
    let archive = fs::read(fixture().join("input-closure.tar.gz")).unwrap();

    // One flipped byte anywhere changes the archive hash.
    let mut flipped = archive.clone();
    let middle = flipped.len() / 2;
    flipped[middle] ^= 1;
    let message = panic_message(std::panic::catch_unwind(|| {
        extract_archive(&provenance, &flipped, true)
    }));
    assert!(
        message.contains("differs from provenance.json"),
        "{message}"
    );

    // Behind the archive hash, each member is checked on its own: a changed
    // file, a missing file, and an unrecorded file are each refused.
    let mut raw = Vec::new();
    flate2::read::GzDecoder::new(archive.as_slice())
        .read_to_end(&mut raw)
        .unwrap();
    let repack = |edit: &dyn Fn(&str, &mut Vec<u8>) -> bool, extra: Option<&str>| {
        let mut builder = tar::Builder::new(flate2::write::GzEncoder::new(
            Vec::new(),
            flate2::Compression::fast(),
        ));
        let mut append = |path: &str, bytes: &[u8]| {
            let mut header = tar::Header::new_ustar();
            header.set_size(bytes.len() as u64);
            header.set_mode(0o644);
            header.set_cksum();
            builder.append_data(&mut header, path, bytes).unwrap();
        };
        for entry in tar::Archive::new(raw.as_slice()).entries().unwrap() {
            let mut entry = entry.unwrap();
            let path = entry.path().unwrap().to_str().unwrap().to_string();
            let mut bytes = Vec::new();
            entry.read_to_end(&mut bytes).unwrap();
            if edit(&path, &mut bytes) {
                append(&path, &bytes);
            }
        }
        if let Some(path) = extra {
            append(path, b"int unrecorded;\n");
        }
        builder.into_inner().unwrap().finish().unwrap()
    };
    let cases: [(Vec<u8>, &str); 3] = [
        (
            repack(
                &|path, bytes| {
                    if path == "include/linux/rbtree.h" {
                        bytes[0] ^= 1;
                    }
                    true
                },
                None,
            ),
            "include/linux/rbtree.h: content differs",
        ),
        (
            repack(&|path, _| path != "include/linux/rbtree_types.h", None),
            "recorded inputs missing from the closure",
        ),
        (
            repack(&|_, _| true, Some("include/linux/unrecorded.h")),
            "include/linux/unrecorded.h: not a recorded input",
        ),
    ];
    for (tampered, expected) in cases {
        let message = panic_message(std::panic::catch_unwind(|| {
            extract_archive(&provenance, &tampered, false)
        }));
        assert!(message.contains(expected), "{expected}: {message}");
    }
}

#[test]
fn linux_rbtree_closure_matches_its_provenance() {
    let provenance = provenance();
    let closure = extract_closure(&provenance);
    let files = provenance["closure"]["files"].as_array().unwrap();
    assert_eq!(
        files.len() as u64,
        provenance["closure"]["file_count"].as_u64().unwrap()
    );
    assert!(closure.0.join("lib/rbtree.c").is_file());

    // The import configuration names the recorded invocation: every recorded
    // argument, in order, except `-E` and the source operand, which the
    // importer supplies itself.
    let config: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture().join("rbtree.click.import.json")).unwrap())
            .unwrap();
    let mut recorded = provenance["preprocess"]["argv"]
        .as_array()
        .unwrap()
        .iter()
        .map(|argument| argument.as_str().unwrap())
        .filter(|argument| *argument != "-E")
        .collect::<Vec<_>>();
    assert_eq!(recorded.pop(), Some("lib/rbtree.c"));
    let configured = config["sources"][0]["args"]
        .as_array()
        .unwrap()
        .iter()
        .map(|argument| argument.as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(configured, recorded);
    assert_eq!(
        config["compiler"].as_str().unwrap(),
        text(&provenance, &["preprocess", "program"])
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn linux_rbtree_pinned_translation_unit_locks_and_reproduces_its_frontier() {
    let provenance = provenance();
    let closure = import_layout(&provenance, &["rbtree.click", "rbtree.click.import.json"]);
    let required = std::env::var_os(REQUIRE_TOOLCHAIN).is_some_and(|value| !value.is_empty());
    if let Some(notice) =
        toolchain_gate(&provenance, required).unwrap_or_else(|error| panic!("{error}"))
    {
        eprintln!("{notice}");
        return;
    }

    // The import route: `click import lock` runs the configured vector
    // under the option profile and reproduces the committed lock.
    let config_path = closure.0.join("rbtree.click.import.json");
    create_lock(&config_path).expect("lock the recorded configuration");
    let artifact = fs::read(closure.0.join("rbtree.i")).unwrap();
    assert_eq!(
        sha256(&artifact),
        text(&provenance, &["preprocess", "output", "sha256"]),
        "the importer's artifact differs from the recorded preprocessed output"
    );
    let produced = read_lock(&closure.0.join("rbtree.click.import.lock.json"));
    let committed = read_lock(&fixture().join("rbtree.click.import.lock.json"));
    for field in [
        "schema",
        "config_sha256",
        "target",
        "compiler_path",
        "option_profile",
        "toolchain",
    ] {
        assert_eq!(
            produced[field], committed[field],
            "lock field `{field}` differs"
        );
    }
    for field in [
        "args",
        "artifact_sha256",
        "artifact_bytes",
        "source_sha256",
        "local_dependencies",
    ] {
        assert_eq!(
            produced["sources"][0][field], committed["sources"][0][field],
            "locked source field `{field}` differs"
        );
    }
    let imports = load_imports(&config_path).expect("load the fresh lock");
    assert_eq!(
        imports[0].promise_attributes(),
        syntax::PromiseAttributes::Refuse
    );
    let inputs = closure.0.join("inputs");

    // The recorded preprocessing, run directly, reproduces the recorded
    // artifact from the closure alone.
    let mut command = Command::new(text(&provenance, &["preprocess", "program"]));
    command.current_dir(&inputs).env_clear();
    for argument in provenance["preprocess"]["argv"].as_array().unwrap() {
        command.arg(argument.as_str().unwrap());
    }
    for (name, value) in provenance["preprocess"]["environment"].as_object().unwrap() {
        command.env(name, value.as_str().unwrap());
    }
    let output = command.output().expect("run the recorded compiler");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.stdout.len() as u64,
        provenance["preprocess"]["output"]["bytes"]
            .as_u64()
            .unwrap()
    );
    assert_eq!(
        sha256(&output.stdout),
        text(&provenance, &["preprocess", "output", "sha256"]),
        "the preprocessed translation unit differs from the recorded artifact"
    );
}

/// The committed lock and artifact load offline, without the recorded
/// compiler: the closure in `inputs/` is checked against the lock, the
/// dependency-closure projection is applied, and the projected unit parses
/// with the optimizer-promise attributes refused.
#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn linux_rbtree_locked_import_loads_offline() {
    let provenance = provenance();
    let layout = import_layout(
        &provenance,
        &[
            "rbtree.click",
            "rbtree.click.import.json",
            "rbtree.click.import.lock.json",
            "rbtree.i",
        ],
    );
    let config_path = layout.0.join("rbtree.click.import.json");
    let imports = load_imports(&config_path).expect("load the committed lock offline");
    assert_eq!(imports.len(), 1);
    let import = imports[0].clone();
    assert_eq!(import.logical_source(), "lib/rbtree.c");
    assert_eq!(
        import.promise_attributes(),
        syntax::PromiseAttributes::Refuse
    );
    let functions = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            syntax::parse_translation_unit_for_import(
                import.source(),
                import.logical_source(),
                import.source_map(),
                import.promise_attributes(),
            )
            .map(|unit| {
                unit.functions
                    .iter()
                    .map(|function| function.name().to_string())
                    .collect::<BTreeSet<_>>()
            })
            .map_err(|error| error.to_string())
        })
        .expect("spawn the locked parse")
        .join()
        .expect("the locked parse finishes")
        .unwrap_or_else(|error| panic!("the locked projected unit no longer parses: {error}"));
    assert_eq!(
        functions,
        PROJECTED_FUNCTIONS
            .iter()
            .map(|name| name.to_string())
            .collect::<BTreeSet<_>>()
    );

    // A changed input header cannot reuse the lock.
    let header = layout.0.join("inputs/include/linux/rbtree.h");
    let original = fs::read(&header).unwrap();
    let mut changed = original.clone();
    changed[0] ^= 1;
    fs::write(&header, changed).unwrap();
    let error = load_imports(&config_path).expect_err("a changed header must be refused");
    assert!(error.contains("differs from its import lock"), "{error}");
    fs::write(&header, original).unwrap();
    load_imports(&config_path).unwrap();
}

/// The locked artifact's frontier: the whole unit stops at its first
/// unsupported declaration, and the projection keeps what the rbtree
/// functions need.
#[test]
fn linux_rbtree_locked_artifact_frontier() {
    assert_eq!(
        sha256(&fs::read(fixture().join("rbtree.i")).unwrap()),
        text(&provenance(), &["preprocess", "output", "sha256"]),
        "the committed artifact is the recorded preprocessed output"
    );
    let artifact = fs::read_to_string(fixture().join("rbtree.i")).expect("the locked artifact");
    let (source, map) = CSourceMap::decode(&artifact).expect("decode line markers");
    let error = match syntax::parse_translation_unit_for_import(
        &source,
        "lib/rbtree.c",
        &map,
        syntax::PromiseAttributes::Refuse,
    ) {
        Ok(_) => panic!(
            "the whole pinned translation unit now parses; drop the projection or update FIRST_REJECTION"
        ),
        Err(error) => error.to_string(),
    };
    assert_eq!(
        error, FIRST_REJECTION,
        "the first rejection moved; update the pin and the inventory in issues/kernel-scale-preprocessing.md"
    );

    // The dependency-closure projection keeps the definitions in
    // `lib/rbtree.c` and what they name; everything it keeps must parse.
    let projection = super::projection::project_dependency_closure(&source, &map)
        .expect("project the pinned translation unit");
    let projected = projection.text.clone();
    let projected_map = map.clone();
    let unit = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            syntax::parse_translation_unit_for_import(
                &projected,
                "lib/rbtree.c",
                &projected_map,
                syntax::PromiseAttributes::Refuse,
            )
            .map(|unit| {
                unit.functions
                    .iter()
                    .map(|function| function.name().to_string())
                    .collect::<BTreeSet<_>>()
            })
            .map_err(|error| error.to_string())
        })
        .expect("spawn the projected parse")
        .join()
        .expect("the projected parse finishes");
    let functions = unit.unwrap_or_else(|error| {
        panic!("the projected pinned translation unit no longer parses: {error}")
    });
    assert_eq!(
        functions,
        PROJECTED_FUNCTIONS
            .iter()
            .map(|name| name.to_string())
            .collect::<BTreeSet<_>>(),
        "the projected function inventory changed"
    );
    assert_eq!(
        (projection.kept, projection.omitted),
        PROJECTED_ITEMS,
        "the projected declaration counts changed"
    );

    if let Some(path) = std::env::var_os(INVENTORY).filter(|path| !path.is_empty()) {
        // The parser recurses on nested statements, and the expanded kernel
        // bodies nest deeply enough to overflow a default test stack.
        let inventory = std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || rejection_inventory(&source, &map))
            .expect("spawn the inventory thread")
            .join()
            .expect("the inventory thread finishes");
        fs::write(path, inventory).expect("write the inventory");
    }
}

/// Byte ranges of the file-scope declarations and definitions in
/// marker-free preprocessed C: each ends at a file-scope `;` or at the
/// closing brace of a function body.
fn file_scope_items(source: &str) -> Vec<(usize, usize)> {
    let bytes = source.as_bytes();
    let mut items = Vec::new();
    let (mut start, mut depth, mut index) = (0, 0usize, 0);
    let mut last_significant = b' ';
    let mut function_body = false;
    while index < bytes.len() {
        let byte = bytes[index];
        match byte {
            b'"' | b'\'' => {
                index += 1;
                while index < bytes.len() && bytes[index] != byte {
                    if bytes[index] == b'\\' {
                        index += 1;
                    }
                    index += 1;
                }
            }
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth = depth.saturating_sub(1),
            b'{' => {
                if depth == 0 {
                    function_body = last_significant == b')';
                }
                depth += 1;
            }
            b'}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && function_body {
                    items.push((start, index + 1));
                    start = index + 1;
                    function_body = false;
                }
            }
            b';' if depth == 0 => {
                items.push((start, index + 1));
                start = index + 1;
            }
            _ => {}
        }
        if !byte.is_ascii_whitespace() {
            last_significant = byte;
        }
        index += 1;
    }
    if !source[start..].trim().is_empty() {
        items.push((start, bytes.len()));
    }
    items
}

/// One line per file-scope item: its original location, whether the parser
/// accepts it after the accepted items before it, and its first rejection.
///
/// A rejected item is blanked, so a later item that needs it is rejected in
/// turn; an item reports only its first rejection. This is a measurement
/// aid: it parses the growing prefix once per item, which is quadratic and
/// is why the gate does not run it.
fn rejection_inventory(source: &str, map: &CSourceMap) -> String {
    let mut accepted = String::with_capacity(source.len());
    let mut inventory = String::new();
    for (start, end) in file_scope_items(source) {
        let item = &source[start..end];
        let leading = item.len() - item.trim_start().len();
        let line = source[..start + leading]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        let origin = map.lookup(SourcePosition::new(line, 1));
        let base = accepted.len();
        accepted.push_str(item);
        let verdict = match syntax::parse_translation_unit_for_import(
            &accepted,
            "lib/rbtree.c",
            map,
            syntax::PromiseAttributes::Refuse,
        ) {
            Ok(_) => "accepted".to_string(),
            Err(error) => {
                accepted.truncate(base);
                accepted.extend(
                    item.chars()
                        .map(|character| if character == '\n' { '\n' } else { ' ' }),
                );
                error.to_string().replace(['\n', '\t'], " ")
            }
        };
        let excerpt = item
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .chars()
            .take(120)
            .collect::<String>();
        inventory.push_str(&format!("{origin}\t{verdict}\t{excerpt}\n"));
    }
    inventory
}
