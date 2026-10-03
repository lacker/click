use click::languages::rust::{load_import, refresh_import};
use click::surface::C0VerificationSession;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

const SOURCE: &str = include_str!("../examples/basic-rust/borrow.rs");
const SIDECAR: &str = include_str!("../examples/basic-rust/borrow.click");
struct Project {
    root: PathBuf,
}
impl Project {
    fn new(source: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "click-rust-import-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let exporter = std::env::var("CLICK_RUST_EXPORTER")
            .expect("build-rust-exporter.sh supplies CLICK_RUST_EXPORTER");
        fs::write(root.join("borrow.rs"), source).unwrap();
        fs::write(root.join("borrow.click"), SIDECAR).unwrap();
        fs::write(root.join("borrow.click.import.json"), serde_json::to_vec(&serde_json::json!({"schema":2,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"borrow.rs","exporter":exporter,"artifact":"borrow.rs.click-rust.json"})).unwrap()).unwrap();
        Self { root }
    }
    fn config(&self) -> PathBuf {
        self.root.join("borrow.click.import.json")
    }
    fn cli(&self, args: &[&str]) -> std::process::Output {
        Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .arg(self.root.join("borrow.click"))
            .output()
            .unwrap()
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

const CHARON_SOURCE: &str = include_str!("../design/charon-trial/trial.rs");
const CHARON_SIDECAR: &str = include_str!("../design/charon-trial/trial.click");
fn charon_project() -> Project {
    let p = Project::new(CHARON_SOURCE);
    fs::write(p.root.join("trial.rs"), CHARON_SOURCE).unwrap();
    fs::write(p.root.join("borrow.click"), CHARON_SIDECAR).unwrap();
    fs::write(
        p.config(),
        include_bytes!("../design/charon-trial/trial.click.import.json"),
    )
    .unwrap();
    fs::write(
        p.root.join("trial.ullbc"),
        include_bytes!("../design/charon-trial/trial.ullbc"),
    )
    .unwrap();
    fs::write(
        p.config().with_file_name("borrow.click.import.json.lock"),
        include_bytes!("../design/charon-trial/trial.click.import.json.lock"),
    )
    .unwrap();
    p
}
const CHARON_FIELDS_SOURCE: &str = include_str!("../design/charon-trial/array-fields/fields.rs");
const CHARON_FIELDS_SIDECAR: &str =
    include_str!("../design/charon-trial/array-fields/fields.click");
fn charon_fields_project() -> Project {
    let p = Project::new(CHARON_FIELDS_SOURCE);
    for (name, bytes) in [
        ("fields.rs", CHARON_FIELDS_SOURCE.as_bytes()),
        ("borrow.click", CHARON_FIELDS_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/array-fields/fields.click.import.json")
                .as_slice(),
        ),
        (
            "fields.ullbc",
            include_bytes!("../design/charon-trial/array-fields/fields.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/array-fields/fields.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_array_fields_check_bounds_authority_and_frames() {
    let p = charon_fields_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_FIELDS_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_FIELDS_SIDECAR.replace("requires index < 4u64;", "requires index == 4u64;"),
        CHARON_FIELDS_SIDECAR.replace("requires index < 7u64;", "requires index == 4294967296u64;"),
        CHARON_FIELDS_SIDECAR.replace("views state->values[0..4];", ""),
        CHARON_FIELDS_SIDECAR.replace("owns state->values[0..4];", "views state->values[0..4];"),
        CHARON_FIELDS_SIDECAR.replace(
            "ensures state->values[(int32)(uint32)index] == value;",
            "ensures state->values[(int32)(uint32)index] != value;",
        ),
        CHARON_FIELDS_SIDECAR.replace(
            "result == old(state->_0[(int32)(uint32)index])",
            "result != old(state->_0[(int32)(uint32)index])",
        ),
    ] {
        assert_ne!(invalid, CHARON_FIELDS_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
fn charon_array_fields_cli_tools_recheck_borrowed_field_certificates() {
    let p = charon_fields_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "read.contract",
        "write.contract",
        "borrowed_first.contract",
        "borrowed_byte.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_array_fields_live_refresh_and_rejected_owned_operations() {
    let p = charon_fields_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_FIELDS_SIDECAR,
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for source in [
        "pub struct A { pub values:[u32;4] } pub fn bad()->u32 { let x=A{values:[0;4]}; x.values[0] }",
        "pub struct A { pub values:[u32;4] } pub fn bad(x:&A)->u32 { let values=x.values; values[0] }",
        "pub struct A { pub values:[u32;4] } pub fn bad(x:&mut A) { x.values=[0;4]; }",
        "pub struct A { pub values:[u16;4] } pub fn bad(x:&A)->u16 { x.values[0] }",
        "#[repr(C,packed)] pub struct A { pub values:[u32;4] } pub fn bad(x:&A)->u32 { x.values[0] }",
        "pub struct A { pub values:[u32;4] } pub fn bad(x:&A) { x.values[0]=1; }",
    ] {
        fs::remove_file(p.root.join("fields.ullbc")).unwrap();
        fs::write(p.root.join("fields.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(!error.contains("panicked"), "{error}");
        assert!(!p.root.join("fields.ullbc").exists());
        fs::write(p.root.join("fields.rs"), CHARON_FIELDS_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_ARITHMETIC_SOURCE: &str =
    include_str!("../design/charon-trial/arithmetic/arithmetic.rs");
const CHARON_ARITHMETIC_SIDECAR: &str =
    include_str!("../design/charon-trial/arithmetic/arithmetic.click");
fn charon_arithmetic_project() -> Project {
    let p = Project::new(CHARON_ARITHMETIC_SOURCE);
    for (name, bytes) in [
        ("arithmetic.rs", CHARON_ARITHMETIC_SOURCE.as_bytes()),
        ("borrow.click", CHARON_ARITHMETIC_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/arithmetic/arithmetic.click.import.json")
                .as_slice(),
        ),
        (
            "arithmetic.ullbc",
            include_bytes!("../design/charon-trial/arithmetic/arithmetic.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/arithmetic/arithmetic.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_checksum_arithmetic_checks_panic_bounds_and_full_width_values() {
    let p = charon_arithmetic_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_ARITHMETIC_SIDECAR, &prepared).unwrap();
    for claim in [
        "uint32 reduce(uint32 value) { requires value == 4294967295u32; ensures result == 224u32; }",
        "uint64 wide_quotient(uint64 value, uint64 divisor) { requires value == 18446744073709551615u64; requires divisor == 1u64; ensures result == 18446744073709551615u64; }",
        "uint64 wide_left(uint64 value, uint64 count) { requires value == 18446744073709551615u64; requires count == 1u64; ensures result == 18446744073709551614u64; }",
        "uint64 wide_right(uint64 value, uint64 count) { requires value == 18446744073709551615u64; requires count == 63u64; ensures result == 1u64; }",
        "uint16 word_right(uint16 value, uint64 count) { requires value == 65535; requires count == 15u64; ensures result == 1; }",
        "uint8 shifted_byte(uint8 value, uint32 count) { requires value == 128; requires count == 1u32; ensures result == 0; }",
        "uint32 conditional_divide(uint32 value, uint32 divisor, bool skip) { requires skip != 0; requires divisor == 0u32; ensures result == 0u32; }",
    ] {
        let claim = format!("verifying \"arithmetic.rs\"; {claim} by {{ execute(); simp(); }}");
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for invalid in [
        CHARON_ARITHMETIC_SIDECAR.replace("requires sum <= 4294967040u32;", ""),
        CHARON_ARITHMETIC_SIDECAR.replace("requires count < 8u32;", "requires count == 8u32;"),
        CHARON_ARITHMETIC_SIDECAR.replace("requires count < 64u64;", "requires count == 64u64;"),
        CHARON_ARITHMETIC_SIDECAR.replace(
            "requires 0 <= count and count < 32;",
            "requires count == -1;",
        ),
        CHARON_ARITHMETIC_SIDECAR.replace("requires divisor != 0u32;", "requires divisor == 0u32;"),
        CHARON_ARITHMETIC_SIDECAR.replace("requires divisor != 0u64;", "requires divisor == 0u64;"),
        CHARON_ARITHMETIC_SIDECAR.replace("value % 65521u32", "value % 65519u32"),
        CHARON_ARITHMETIC_SIDECAR.replace("((high << 16) | low)", "((high << 15) | low)"),
    ] {
        assert_ne!(invalid, CHARON_ARITHMETIC_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    for count in [64u64, 4294967296, u64::MAX] {
        let claim = format!(
            "verifying \"arithmetic.rs\"; uint64 wide_left(uint64 value, uint64 count) {{ requires value == 0u64; requires count == {count}u64; ensures result == 0u64; }} by {{ execute(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&claim, &prepared)
            .err()
            .expect("invalid shift accepted");
        assert!(
            error.message().contains("Rust shl panic check"),
            "{}",
            error.message()
        );
    }
}
#[test]
fn charon_checksum_arithmetic_cli_tools_recheck_certificates() {
    let p = charon_arithmetic_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "reduce.contract",
        "pack.contract",
        "wide_left.contract",
        "signed_count.contract",
        "conditional_divide.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
fn rust_and_charon_unsigned_shifts_preserve_full_width_counts() {
    let p = Project::new(CHARON_ARITHMETIC_SOURCE);
    refresh_import(&p.config()).unwrap();
    let sidecar = CHARON_ARITHMETIC_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &load_import(&p.config()).unwrap())
        .unwrap();
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_checksum_arithmetic_live_refresh_and_rejected_modes() {
    let p = charon_arithmetic_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_ARITHMETIC_SIDECAR,
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for source in [
        "pub fn bad(x:u32, count:u32)->u32 { x.wrapping_shl(count) }",
        "pub fn bad(x:u32, count:u32)->u32 { x.wrapping_shr(count) }",
        "pub fn bad(x:i32, count:u32)->i32 { x << count }",
        "pub fn bad(x:i32, divisor:i32)->i32 { x / divisor }",
    ] {
        fs::remove_file(p.root.join("arithmetic.ullbc")).unwrap();
        fs::write(p.root.join("arithmetic.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains("Charon trial does not support"), "{error}");
        assert!(!p.root.join("arithmetic.ullbc").exists());
        fs::write(p.root.join("arithmetic.rs"), CHARON_ARITHMETIC_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_NESTED_SOURCE: &str = include_str!("../design/charon-trial/nested/nested.rs");
const CHARON_NESTED_SIDECAR: &str = include_str!("../design/charon-trial/nested/nested.click");
fn charon_nested_project() -> Project {
    let p = Project::new(CHARON_NESTED_SOURCE);
    for (name, bytes) in [
        ("nested.rs", CHARON_NESTED_SOURCE.as_bytes()),
        ("borrow.click", CHARON_NESTED_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/nested/nested.click.import.json").as_slice(),
        ),
        (
            "nested.ullbc",
            include_bytes!("../design/charon-trial/nested/nested.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/nested/nested.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_nested_chunks_and_array_slices_check_bytes_bounds_and_claims() {
    let p = charon_nested_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_NESTED_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_NESTED_SIDECAR.replace("ensures result == 8u64;", "ensures result == 7u64;"),
        CHARON_NESTED_SIDECAR.replace("ensures result == 9;", "ensures result == 7;"),
        CHARON_NESTED_SIDECAR.replace("requires index < 8u64;", "requires index == 8u64;"),
        CHARON_NESTED_SIDECAR.replace("ensures result == 7;", "ensures result == 9;"),
        CHARON_NESTED_SIDECAR.replace("views bytes[0..8];", ""),
        CHARON_NESTED_SIDECAR.replace("bytes[k] == old(bytes[k])", "bytes[k] == 7"),
    ] {
        assert_ne!(invalid, CHARON_NESTED_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
fn charon_nested_cli_tools_recheck_expanded_certificates() {
    let p = charon_nested_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "nested.contract",
        "array_len.contract",
        "array_mut.contract",
        "array_read.contract",
        "large_array_len.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_nested_live_refresh_and_rejected_array_borrows() {
    let p = charon_nested_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_NESTED_SIDECAR,
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        (
            "pub fn bad()->u8 { let mut bytes=[7u8;8]; let slice:&[u8]=&bytes; bytes[0]=9; slice[0] }",
            "E0506",
        ),
        (
            "pub fn bad()->u8 { let bytes=[7u8;8]; let slice:&[u8]=&bytes; slice[0]=9; slice[0] }",
            "E0594",
        ),
        (
            "pub fn bad()->usize { let bytes=[7u16;8]; let slice:&[u16]=&bytes; slice.len() }",
            "Charon trial does not support",
        ),
        (
            "pub fn bad(n:i32) { let mut i=0; while i<n { let mut j=0; while j<n { if j==2 { break; } j+=1; } i+=1; } }",
            "extra exit",
        ),
    ] {
        fs::remove_file(p.root.join("nested.ullbc")).unwrap();
        fs::write(p.root.join("nested.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("nested.ullbc").exists());
        fs::write(p.root.join("nested.rs"), CHARON_NESTED_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_CHUNK_SOURCE: &str = include_str!("../design/charon-trial/chunks/chunks.rs");
const CHARON_CHUNK_SIDECAR: &str = include_str!("../design/charon-trial/chunks/chunks.click");
fn charon_chunk_project() -> Project {
    let p = Project::new(CHARON_CHUNK_SOURCE);
    for (name, bytes) in [
        ("chunks.rs", CHARON_CHUNK_SOURCE.as_bytes()),
        ("borrow.click", CHARON_CHUNK_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/chunks/chunks.click.import.json").as_slice(),
        ),
        (
            "chunks.ullbc",
            include_bytes!("../design/charon-trial/chunks/chunks.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/chunks/chunks.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_chunks_check_boundaries_authority_and_false_claims() {
    let p = charon_chunk_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_CHUNK_SIDECAR, &prepared).unwrap();
    for (length, size) in [
        (0u64, 4u64),
        (4, 4),
        (7, 4),
        (8, 4),
        (3, 4),
        (7, u64::MAX),
        (7, 4294967296),
    ] {
        let claim = format!(
            "verifying \"chunks.rs\"; uint64 tail(const uint8* bytes, uint64 bytes_len, uint64 size) {{ requires bytes_len == {length}u64; requires size == {size}u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length % size
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for length in [0u64, 3, 4, 7, 8] {
        let result = if length < 4 { 0 } else { 4 };
        let claim = format!(
            "verifying \"chunks.rs\"; uint64 next_len(const uint8* bytes, uint64 bytes_len) {{ requires bytes_len == {length}u64; ensures result == {result}u64; }} by {{ execute(); simp(); }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for length in [1u64, 3, 5, 7] {
        let offset = length - length % 4;
        let claim = format!(
            "verifying \"chunks.rs\"; uint8 tail_byte(const uint8* bytes, uint64 bytes_len) {{ requires bytes_len == {length}u64; views bytes[0..{length}]; ensures result == old(bytes[{offset}]); }} by {{ have ((int32)(uint32)(bytes_len - bytes_len % 4u64)) == {offset} by {{ rewrite(bytes_len == {length}u64); simp(); }} execute(); simp(); }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for invalid in [
        CHARON_CHUNK_SIDECAR.replace("requires size != 0u64;", "requires size == 0u64;"),
        CHARON_CHUNK_SIDECAR.replace(
            "ensures result == bytes_len % size;",
            "ensures result == bytes_len;",
        ),
        CHARON_CHUNK_SIDECAR.replace("    requires bytes_len <= 2147483647u64;\n", ""),
        CHARON_CHUNK_SIDECAR.replace("    views bytes[0..(int32)(uint32)bytes_len];\n", ""),
        CHARON_CHUNK_SIDECAR.replace("requires bytes_len == 7u64;", "requires bytes_len == 8u64;"),
        CHARON_CHUNK_SIDECAR.replace("ensures result == old(bytes[4]);", "ensures result == 7;"),
    ] {
        assert_ne!(invalid, CHARON_CHUNK_SIDECAR);
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {invalid}"
        );
    }
}
#[test]
fn charon_chunk_cli_tools_recheck_expanded_certificates() {
    let p = charon_chunk_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "tail.contract",
        "walk.contract",
        "next_len.contract",
        "tail_byte.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_chunks_live_refresh_and_rejected_protocols() {
    let p = charon_chunk_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_CHUNK_SIDECAR,
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        (
            "pub fn bad(x:&[u8]) { let chunks=x.chunks_exact(4); for chunk in chunks { chunk[0]=7; } }",
            "E0594",
        ),
        (
            "pub fn bad(x:&[u8])->usize { let chunks=x.chunks_exact(4); for chunk in chunks { let a=chunk[0]; } chunks.remainder().len() }",
            "E0382",
        ),
        (
            "pub fn bad(x:&[u16])->usize { x.chunks_exact(4).remainder().len() }",
            "Charon trial does not support",
        ),
        (
            "pub fn bad(x:&[u8]) { for chunk in x.chunks_exact(4).rev() { let a=chunk[0]; } }",
            "Charon trial does not support",
        ),
    ] {
        fs::remove_file(p.root.join("chunks.ullbc")).unwrap();
        fs::write(p.root.join("chunks.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("chunks.ullbc").exists());
        fs::write(p.root.join("chunks.rs"), CHARON_CHUNK_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_SLICE_SOURCE: &str = include_str!("../design/charon-trial/slices/slices.rs");
const CHARON_SLICE_SIDECAR: &str = include_str!("../design/charon-trial/slices/slices.click");
fn charon_slice_project() -> Project {
    let p = Project::new(CHARON_SLICE_SOURCE);
    for (name, bytes) in [
        ("slices.rs", CHARON_SLICE_SOURCE.as_bytes()),
        ("borrow.click", CHARON_SLICE_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/slices/slices.click.import.json").as_slice(),
        ),
        (
            "slices.ullbc",
            include_bytes!("../design/charon-trial/slices/slices.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/slices/slices.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_slices_preserve_metadata_permissions_and_cleanup() {
    let p = charon_slice_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_SLICE_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_SLICE_SIDECAR.replace("ensures result == bytes_len;", "ensures result == 0;"),
        CHARON_SLICE_SIDECAR.replace("ensures result == value;", "ensures result == value + 1;"),
        CHARON_SLICE_SIDECAR.replace(
            "ensures value[0] == old(value[0]);",
            "ensures value[0] == 7;",
        ),
        CHARON_SLICE_SIDECAR.replace("    requires index < bytes_len;\n", ""),
        CHARON_SLICE_SIDECAR.replace(
            "    requires index < bytes_len;",
            "    requires index == bytes_len;",
        ),
        CHARON_SLICE_SIDECAR.replace(
            "    requires index < bytes_len;",
            "    requires index == 4294967296u64;",
        ),
        CHARON_SLICE_SIDECAR.replace("    requires bytes_len <= 2147483647u64;\n", ""),
        CHARON_SLICE_SIDECAR.replace("    views bytes[0..(int32)(uint32)bytes_len];\n", ""),
        CHARON_SLICE_SIDECAR.replace("    owns bytes[0..(int32)(uint32)bytes_len];\n", ""),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {invalid}"
        );
    }
    // Contract owns/views composition already establishes byte separation.
    let composed = CHARON_SLICE_SIDECAR.replace(
        "    requires separate(memory(value[0..1]), memory(bytes[0..(int32)(uint32)bytes_len]));\n",
        "",
    );
    C0VerificationSession::new_program_prepared(&composed, &prepared).unwrap();
    // Metadata alone requires no memory resource, including empty and very large slices.
    for length in [0u64, 8, 1024, 1_000_000, u64::MAX] {
        let claim = format!(
            "verifying \"slices.rs\"; uint64 length(const uint8* bytes, uint64 bytes_len) {{ requires bytes_len == {length}u64; ensures result == {length}u64; }} by {{ execute(); simp(); }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
}
#[test]
fn charon_slice_failure_does_not_suggest_unsupported_trace() {
    let p = charon_slice_project();
    fs::write(
        p.root.join("borrow.click"),
        CHARON_SLICE_SIDECAR.replace("ensures result == bytes_len;", "ensures result == 0;"),
    )
    .unwrap();
    let output = p.cli(&["verify"]);
    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("proof error:"), "{error}");
    assert!(!error.contains("--trace-proof"), "{error}");
}
#[test]
fn charon_slice_cli_tools_recheck_expanded_certificates() {
    let p = charon_slice_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "length.contract",
        "write_read.contract",
        "guarded_read.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_slices_live_refresh_and_borrow_checking() {
    let p = charon_slice_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_SLICE_SIDECAR,
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        ("pub fn bad(x:&[u8]) { x[0]=7; }", "E0594"),
        (
            "pub fn bad(x:&mut [u8]) -> u8 { let y=&mut *x; x[0]=7; y[0] }",
            "E0503",
        ),
        (
            "pub fn bad(x:&[u16])->usize { x.len() }",
            "slice elements other than u8",
        ),
    ] {
        fs::remove_file(p.root.join("slices.ullbc")).unwrap();
        fs::write(p.root.join("slices.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("slices.ullbc").exists());
        fs::write(p.root.join("slices.rs"), CHARON_SLICE_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_ARRAY_SOURCE: &str =
    include_str!("../design/charon-trial/conversions-arrays/arrays.rs");
const CHARON_ARRAY_SIDECAR: &str =
    include_str!("../design/charon-trial/conversions-arrays/arrays.click");
fn charon_array_project() -> Project {
    let p = Project::new(CHARON_ARRAY_SOURCE);
    for (name, bytes) in [
        ("arrays.rs", CHARON_ARRAY_SOURCE.as_bytes()),
        ("borrow.click", CHARON_ARRAY_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/conversions-arrays/arrays.click.import.json")
                .as_slice(),
        ),
        (
            "arrays.ullbc",
            include_bytes!("../design/charon-trial/conversions-arrays/arrays.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../design/charon-trial/conversions-arrays/arrays.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_arrays_compose_with_resolved_conversion_and_drop() {
    let p = charon_array_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_ARRAY_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_ARRAY_SIDECAR.replace("ensures result == x;", "ensures result == x + 1;"),
        CHARON_ARRAY_SIDECAR.replace("value[0] == old(value[0]);", "value[0] == 7;"),
        CHARON_ARRAY_SIDECAR.replace("ensures result == 7;", "ensures result == 8;"),
        CHARON_ARRAY_SIDECAR.replace("ensures result == 9;", "ensures result == 2;"),
        CHARON_ARRAY_SIDECAR.replace("ensures result == 1;", "ensures result == 257;"),
        CHARON_ARRAY_SIDECAR.replace(
            "value[0] == old(value[0]) + 1;",
            "value[0] == old(value[0]);",
        ),
        CHARON_ARRAY_SIDECAR.replace("    owns value[0..1];\n", ""),
        CHARON_ARRAY_SIDECAR.replace("    requires value[0] < 2147483647;\n", ""),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {invalid}"
        );
    }
}
#[test]
fn charon_array_cli_tools_recheck_expanded_certificates() {
    let p = charon_array_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "guarded_array.contract",
        "large_array.contract",
        "empty_array.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_arrays_live_refresh_and_rejected_source_shapes() {
    let p = charon_array_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_ARRAY_SIDECAR,
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        ("pub fn bad(x:u32)->u8 { u8::from(x) }", "E0277"),
        (
            "struct Fake; impl Fake { fn from(x:u16)->u32 { x as u32 } } pub fn bad(x:u16)->u32 { Fake::from(x) }",
            "nested or disambiguated source items",
        ),
        ("pub fn bad()->u16 { let x=[7u16;4]; x[0] }", "i32/u8/u32"),
        (
            "pub fn bad()->u32 { let x=[7u32;536870912]; x[0] }",
            "signed-word storage",
        ),
    ] {
        fs::remove_file(p.root.join("arrays.ullbc")).unwrap();
        fs::write(p.root.join("arrays.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("arrays.ullbc").exists());
        fs::write(p.root.join("arrays.rs"), CHARON_ARRAY_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_LOOP_SOURCE: &str = include_str!("../design/charon-trial/borrowed-loop/loop.rs");
const CHARON_LOOP_SIDECAR: &str = include_str!("../design/charon-trial/borrowed-loop/loop.click");
fn charon_loop_project() -> Project {
    let p = Project::new(CHARON_LOOP_SOURCE);
    fs::write(p.root.join("loop.rs"), CHARON_LOOP_SOURCE).unwrap();
    fs::write(p.root.join("borrow.click"), CHARON_LOOP_SIDECAR).unwrap();
    fs::write(
        p.config(),
        include_bytes!("../design/charon-trial/borrowed-loop/loop.click.import.json"),
    )
    .unwrap();
    fs::write(
        p.root.join("loop.ullbc"),
        include_bytes!("../design/charon-trial/borrowed-loop/loop.ullbc"),
    )
    .unwrap();
    fs::write(
        p.config().with_file_name("borrow.click.import.json.lock"),
        include_bytes!("../design/charon-trial/borrowed-loop/loop.click.import.json.lock"),
    )
    .unwrap();
    p
}
#[test]
fn charon_borrowed_loop_checks_restoration_bounds_and_ranking() {
    let p = charon_loop_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_LOOP_SIDECAR, &prepared).unwrap();
    for n in [0, 1, 2147483647] {
        let concrete =
            CHARON_LOOP_SIDECAR.replace("requires n >= 0;", &format!("requires n == {n};"));
        C0VerificationSession::new_program_prepared(&concrete, &prepared).unwrap();
    }
    for invalid in [
        CHARON_LOOP_SIDECAR.replace("result == n", "result == n + 1"),
        CHARON_LOOP_SIDECAR.replace("value[0] == old(value[0])", "value[0] == 7"),
        CHARON_LOOP_SIDECAR.replace("requires n >= 0;", "requires n == -1;"),
        CHARON_LOOP_SIDECAR.replace(
            "invariant 0 <= i and i <= n;",
            "invariant 0 <= i and i < n;",
        ),
        CHARON_LOOP_SIDECAR.replace("decreases n - i;", "decreases i;"),
        CHARON_LOOP_SIDECAR.replace("    owns value[0..1];\n", ""),
        CHARON_LOOP_SIDECAR.replace("execute_until(loop(0))", "execute_until(loop(99))"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
fn charon_borrowed_loop_cli_expands_checked_loop_certificate() {
    let p = charon_loop_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    assert_cli(
        &p,
        &["expand", "--claim", "guarded_walk.contract", "--in-place"],
    );
    assert_cli(&p, &["verify"]);
    fs::write(
        p.root.join("borrow.click"),
        CHARON_LOOP_SIDECAR.replace("requires n >= 0;", "requires n == 0;"),
    )
    .unwrap();
    assert_cli(&p, &["verify"]);
    assert_cli(
        &p,
        &["expand", "--claim", "guarded_walk.contract", "--in-place"],
    );
    assert_cli(&p, &["verify"]);
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_borrowed_loop_live_refresh_and_rejected_control_flow() {
    let p = charon_loop_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_LOOP_SIDECAR, &prepared).unwrap();
    for (source, diagnostic) in [
        (
            CHARON_LOOP_SOURCE.replace(
                "        *slot = i;",
                "        *value = 0;\n        *slot = i;",
            ),
            "E0506",
        ),
        (
            "pub fn bad(n:i32) { let mut i=0; while i<n { if i==2 { break; } i+=1; } }".into(),
            "extra exit",
        ),
        (
            "pub fn bad(n:&i32) { let mut i=0; while i<*n { i+=1; } }".into(),
            "pure scalar",
        ),
    ] {
        fs::remove_file(p.root.join("loop.ullbc")).unwrap();
        fs::write(p.root.join("loop.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("loop.ullbc").exists());
        fs::write(p.root.join("loop.rs"), CHARON_LOOP_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

#[test]
fn charon_trial_checks_arithmetic_and_owned_cleanup_through_shared_engine() {
    let p = charon_project();
    let prepared = load_import(&p.config()).unwrap();
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .all(|f| f.mir.is_some() && f.body.is_empty())
    );
    C0VerificationSession::new_program_prepared(CHARON_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_SIDECAR.replace("result == x + 1", "result == x + 2"),
        CHARON_SIDECAR.replace("    requires x < 65535;\n", ""),
        CHARON_SIDECAR.replace(
            "uint16 guarded_increment(uint16 x, int32* value, bool early) {\n    requires x < 65535;",
            "uint16 guarded_increment(uint16 x, int32* value, bool early) {",
        ),
        CHARON_SIDECAR.replace("value[0] == old(value[0])", "value[0] == 7"),
        CHARON_SIDECAR.replace("    owns value[0..1];\n", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
fn charon_trial_cli_tools_and_expanded_certificate_agree() {
    let p = charon_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    assert_cli(
        &p,
        &[
            "expand",
            "--claim",
            "guarded_increment.contract",
            "--in-place",
        ],
    );
    assert_cli(&p, &["verify"]);
}
#[test]
fn charon_trial_lock_rejects_source_and_profile_changes() {
    let p = charon_project();
    fs::write(
        p.root.join("trial.rs"),
        format!("{CHARON_SOURCE}\n// changed"),
    )
    .unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
    fs::write(p.root.join("trial.rs"), CHARON_SOURCE).unwrap();
    let c = fs::read(p.config()).unwrap();
    fs::write(
        p.config(),
        String::from_utf8(c)
            .unwrap()
            .replace("charon-trial", "other"),
    )
    .unwrap();
    assert!(load_import(&p.config()).is_err());
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler; run explicitly after scripts/build-charon.sh"]
fn charon_trial_live_refresh_and_compiler_rejections() {
    let p = charon_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_SIDECAR, &prepared).unwrap();
    for (source, expected) in [
        (
            include_str!("../design/borrow-probes/charon-borrow-rejected.rs"),
            "E0506",
        ),
        (
            include_str!("../design/borrow-probes/charon-move-rejected.rs"),
            "E0382",
        ),
        ("pub fn unsupported(x: u64) -> u64 { x }", "integer width"),
    ] {
        fs::remove_file(p.root.join("trial.ullbc")).unwrap();
        fs::write(p.root.join("trial.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(!p.root.join("trial.ullbc").exists());
        fs::write(p.root.join("trial.rs"), CHARON_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}
#[test]
fn rust_typed_import_verifies_borrow_parent_reuse_and_field_frame() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    assert_eq!(verified.len(), 12);
    let false_claim = SIDECAR.replace("ensures result == 8;", "ensures result == 9;");
    assert!(C0VerificationSession::new_program_prepared(&false_claim, &prepared).is_err());
}
#[test]
fn rust_lock_rejects_changed_source_and_artifact() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    fs::write(p.root.join("borrow.rs"), format!("{SOURCE}\n// changed")).unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
    fs::write(p.root.join("borrow.rs"), SOURCE).unwrap();
    fs::write(p.root.join("borrow.rs.click-rust.json"), b"{}").unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
}
#[test]
fn rust_compiler_and_subset_rejections_are_distinct() {
    for (source, diagnostic) in [
        (
            "pub fn bad(p: &mut i32) { let child = &mut *p; *p = 4; *child = 7; }",
            "cannot assign",
        ),
        ("pub fn bad(x: u64) -> u64 { x }", "unsupported Rust type"),
        (
            "pub fn bad(mut x: i32) -> i32 { loop { x += 1; } }",
            "unlabeled Rust while",
        ),
        (
            "mod other; pub fn ok(x:i32)->i32{x}",
            "Rust source boundary",
        ),
        (
            "pub fn ok(x:i32)->i32 { include!(\"other.rs\") }",
            "Rust source boundary",
        ),
        ("pub unsafe fn bad(x:i32)->i32{x}", "unsafe or generic"),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
        assert!(!p.root.join("borrow.rs.click-rust.json").exists());
    }
}
fn assert_cli(p: &Project, args: &[&str]) {
    let result = p.cli(args);
    assert!(
        result.status.success(),
        "{args:?}: stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}
#[test]
fn rust_ordinary_cli_locks_and_verifies() {
    let p = Project::new(SOURCE);
    assert_cli(&p, &["import", "lock"]);
    assert_cli(&p, &["verify"]);
}
#[test]
fn rust_cli_profile_and_audit_use_the_shared_engine() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
}
#[test]
fn rust_cli_expansion_reverifies_through_ordinary_entry() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["expand", "--claim", "update.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_checked_arithmetic_requires_a_panic_freedom_bound() {
    let p = Project::new("pub fn increment(x:i32)->i32 { x + 1 }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let claim = "verifying \"borrow.rs\"; int32 increment(int32 x) { ensures result == x + 1; } by { execute(); simp(); }";
    assert!(C0VerificationSession::new_program_prepared(claim, &prepared).is_err());
    let bounded = claim.replace("ensures result", "requires x < 2147483647; ensures result");
    C0VerificationSession::new_program_prepared(&bounded, &prepared).unwrap();
}

#[test]
fn rust_boolean_return_and_local_initialization_verify() {
    let p = Project::new("pub fn invert(x:bool)->bool { let answer = !x; answer }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let claim = "verifying \"borrow.rs\"; bool invert(bool x) { ensures result == (if x != 0 { 0 } else { 1 }); } by { if x == 0 { execute(); simp(); } else { execute(); simp(); } }";
    C0VerificationSession::new_program_prepared(claim, &prepared).unwrap();
}

const MOVE_SOURCE: &str = include_str!("../examples/rust-move-drop/guard.rs");
const MOVE_SIDECAR: &str = include_str!("../examples/rust-move-drop/guard.click");
fn moves_project(source: &str) -> (Project, String) {
    let p = Project::new(source);
    let sidecar = MOVE_SIDECAR.replace("guard.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    (p, sidecar)
}
#[test]
fn rust_moves_drop_effect_and_return_capture_verify() {
    let (p, sidecar) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for wrong in [
        sidecar.replace(
            "ensures value[0] == old(value[0]);",
            "ensures value[0] == 7;",
        ),
        sidecar.replace(
            "ensures self->slot[0] == old(self->saved);",
            "ensures self->slot[0] == 7;",
        ),
        sidecar.replace(
            "ensures result == (if early != 0 { 7 } else { 9 });",
            "ensures result == old(value[0]);",
        ),
        sidecar[sidecar.find("int32 restore").unwrap()..]
            .to_string()
            .replace("int32 restore", "verifying \"borrow.rs\"; int32 restore"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&wrong, &prepared).is_err());
    }
    assert_eq!(
        fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
        MOVE_SOURCE
    );
}
#[test]
fn rust_move_borrow_conflicts_and_partial_moves_fail_closed() {
    for (source, diagnostic) in [
        (
            "pub struct S {pub x:i32} pub fn bad()->i32 {let a=S{x:1};let b=a; a.x}",
            "use of moved value",
        ),
        (
            "pub struct S {pub x:i32} pub fn bad()->i32 {let a=S{x:1};let r=&a;let b=a;r.x}",
            "cannot move out",
        ),
        (
            "pub struct S {pub x:i32} pub fn bad(a:S)->i32 {a.x}",
            "Rust value type",
        ),
        (
            "pub struct S<'a> {pub p:&'a mut i32} pub fn bad(p:&mut i32) {let a=S{p};let moved=a.p;*moved=4;}",
            "partial moves",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config())
            .and_then(|_| {
                let prepared = load_import(&p.config())?;
                C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
                    .map(|_| ())
                    .map_err(|e| format!("{e:?}"))
            })
            .unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
    }
}
#[test]
fn rust_move_drop_cli_proofs_expand_and_reverify() {
    let (p, _) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["expand", "--claim", "restore.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

fn replace_artifact(p: &Project, export: &click::languages::rust::schema::RustExport) {
    use sha2::{Digest, Sha256};
    let bytes = serde_json::to_vec(export).unwrap();
    fs::write(p.root.join("borrow.rs.click-rust.json"), &bytes).unwrap();
    let lock_path = p.root.join("borrow.click.import.json.lock");
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(&lock_path).unwrap()).unwrap();
    lock["artifact"] = format!("{:x}", Sha256::digest(&bytes)).into();
    let identity = format!(
        "click-rust-import-v2\n{}\n{}\n{}\n{}\n{}\n{}",
        lock["config"].as_str().unwrap(),
        lock["source"].as_str().unwrap(),
        lock["exporter"].as_str().unwrap(),
        lock["artifact"].as_str().unwrap(),
        click::languages::rust::schema::COMPILER_COMMIT,
        click::languages::rust::schema::TARGET
    );
    lock["identity"] = format!("{:x}", Sha256::digest(identity.as_bytes())).into();
    fs::write(lock_path, serde_json::to_vec(&lock).unwrap()).unwrap();
}
#[test]
fn rust_kernel_rejects_duplicate_move_drop_and_missing_cleanup() {
    use click::languages::rust::schema::{MirStatement as S, MirTerminator as T};
    let (p, sidecar) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    let original = load_import(&p.config()).unwrap().export().clone();
    for corruption in 0..4 {
        let mut export = original.clone();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "restore")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        if corruption == 0 || corruption == 3 {
            let statements = &mut mir.blocks[0].statements;
            let index = statements
                .iter()
                .position(|s| matches!(s, S::Move { .. }))
                .unwrap();
            let extra = if corruption == 0 {
                statements[index].clone()
            } else {
                let S::Move { source, record, .. } = &statements[index] else {
                    unreachable!()
                };
                S::Assign {
                    target: click::languages::rust::schema::Expression::Local {
                        name: "__rust_mir_0".into(),
                    },
                    value: click::languages::rust::schema::Expression::Field {
                        base: Box::new(click::languages::rust::schema::Expression::Local {
                            name: source.clone(),
                        }),
                        record: record.clone(),
                        field: "saved".into(),
                    },
                }
            };
            statements.insert(index + 1, extra);
        } else {
            let index = mir
                .blocks
                .iter()
                .position(|b| matches!(b.terminator, T::Drop { .. }))
                .unwrap();
            let T::Drop {
                local,
                record,
                target,
            } = mir.blocks[index].terminator.clone()
            else {
                unreachable!()
            };
            if corruption == 1 {
                let duplicate = mir.blocks.len();
                mir.blocks.push(click::languages::rust::schema::MirBlock {
                    statements: vec![],
                    terminator: T::Drop {
                        local: local.clone(),
                        record: record.clone(),
                        target,
                    },
                });
                mir.blocks[index].terminator = T::Drop {
                    local,
                    record,
                    target: duplicate,
                };
            } else {
                mir.blocks[index].terminator = T::Goto { target };
            }
        }
        replace_artifact(&p, &export);
        let prepared = load_import(&p.config()).unwrap();
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "corruption {corruption}"
        );
    }
}
#[test]
fn rust_conditional_move_and_explicit_drop_verify() {
    let source = format!(
        "{}    if early {{ let moved = guard; *moved.slot = 7; std::mem::drop(moved); 7 }}\n    else {{ *guard.slot = 9; 9 }}\n}}\n",
        MOVE_SOURCE.split("    let moved = guard;").next().unwrap()
    );
    let (p, sidecar) = moves_project(&source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
}

#[test]
fn rust_owned_field_loan_recovery_verifies() {
    // Preserve the ordinary Rust source that exposed fragmented ownership at
    // the outer destructor call. Do not alter it to make the proof pass.
    let source = format!(
        "{}pub fn cleanup(value:&mut i32) {{ let mut first = Guard {{slot:value,saved:1}}; let second = Guard {{slot:&mut first.saved,saved:42}}; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}void cleanup(int32* value) {{ owns value[0..1]; ensures value[0] == 42; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("int32 restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("value[0] == 42", "value[0] == 1"),
            &prepared
        )
        .is_err()
    );
    assert_eq!(
        fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
        source
    );
}

#[test]
fn rust_owned_field_loan_cli_expands_and_reverifies() {
    let p = Project::new(include_str!("../examples/rust-field-borrow/guard.rs"));
    fs::write(
        p.root.join("borrow.click"),
        include_str!("../examples/rust-field-borrow/guard.click").replace("guard.rs", "borrow.rs"),
    )
    .unwrap();
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "cleanup.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_owned_field_parent_can_write_after_explicit_child_drop() {
    let source = format!(
        "{}pub fn cleanup(value:&mut i32) {{ let mut first = Guard {{slot:value,saved:1}}; let second = Guard {{slot:&mut first.saved,saved:42}}; std::mem::drop(second); first.saved = 43; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}void cleanup(int32* value) {{ owns value[0..1]; ensures value[0] == 43; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("int32 restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
}

#[test]
fn rust_owned_disjoint_mutable_fields_verify() {
    let source = "pub struct Pair {pub x:i32,pub y:i32} pub fn set(left:&mut i32,right:&mut i32) {*left=7;*right=9;} pub fn fields()->i32 {let mut pair=Pair{x:1,y:2}; let left=&mut pair.x; let right=&mut pair.y; set(left,right); if pair.y == 9 {pair.x} else {0}}";
    let p = Project::new(source);
    let sidecar = "verifying \"borrow.rs\"; void set(int32* left,int32* right) {owns left[0..1];owns right[0..1];ensures left[0]==7;ensures right[0]==9;} by {execute();simp();} int32 fields() {ensures result==7;} by {execute();simp();}";
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result==7", "result==0"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_owned_field_conflicting_parent_access_is_rejected_by_compiler() {
    let prefix = MOVE_SOURCE.split("pub fn restore").next().unwrap();
    for (suffix, diagnostic) in [
        ("first.saved=5; std::mem::drop(second);", "cannot assign"),
        (
            "std::mem::drop(first); std::mem::drop(second);",
            "cannot move out",
        ),
        (
            "std::mem::drop(second); *second.slot=5;",
            "use of moved value",
        ),
    ] {
        let source = format!(
            "{prefix}pub fn bad(value:&mut i32) {{ let mut first=Guard{{slot:value,saved:1}}; let second=Guard{{slot:&mut first.saved,saved:42}}; {suffix} }}"
        );
        let p = Project::new(&source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert_eq!(
            fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
            source
        );
    }
}

#[test]
fn rust_moves_plain_struct_and_reads_destination() {
    let p =
        Project::new("pub struct S {pub x:i32} pub fn plain()->i32 {let a=S{x:17}; let b=a; b.x}");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        "verifying \"borrow.rs\"; int32 plain() {ensures result == 17;} by {execute(); simp();}",
        &prepared,
    )
    .unwrap();
}

#[test]
fn rust_two_guards_clean_up_in_reverse_construction_order() {
    use click::languages::rust::schema::{MirStatement as S, MirTerminator as T};
    let source = format!(
        "{}pub fn cleanup(left:&mut i32,right:&mut i32) {{ let first=Guard{{slot:left,saved:17}}; let second=Guard{{slot:right,saved:42}}; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}void cleanup(int32* left,int32* right) {{ owns left[0..1]; owns right[0..1]; ensures left[0] == 17; ensures right[0] == 42; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("int32 restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let mir = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name == "cleanup")
        .unwrap()
        .mir
        .as_ref()
        .unwrap();
    let constructors = mir
        .blocks
        .iter()
        .flat_map(|b| &b.statements)
        .filter_map(|s| match s {
            S::Initialize { target, .. } => Some(target.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut drops = Vec::new();
    let mut block = 0;
    loop {
        match &mir.blocks[block].terminator {
            T::Drop { local, target, .. } => {
                drops.push(local.clone());
                block = *target;
            }
            T::Goto { target } => block = *target,
            T::Return => break,
            _ => panic!("unexpected cleanup edge"),
        }
    }
    assert_eq!(drops, constructors.into_iter().rev().collect::<Vec<_>>());
}

const UNSIGNED_SOURCE: &str = include_str!("../examples/rust-unsigned/arithmetic.rs");
const UNSIGNED_SIDECAR: &str = include_str!("../examples/rust-unsigned/arithmetic.click");

#[test]
fn rust_unsigned_arithmetic_and_expansion_verify() {
    let p = Project::new(UNSIGNED_SOURCE);
    let sidecar = UNSIGNED_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 9);
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 0;", "ensures result == 1;"),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "add_byte.contract",
        "shifted_byte.contract",
        "low_byte.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_unsigned_panic_paths_are_rejected() {
    for (ty, expression, precondition) in [
        ("u32", "x + 1", "x == 4294967295u32"),
        ("u8", "x + 1", "x == 255"),
        ("u32", "x - 1", "x == 0"),
        ("u8", "x - 1", "x == 0"),
        ("u32", "x * 2", "x == 4294967295u32"),
        ("u8", "x * 2", "x == 255"),
        ("u32", "1 / x", "x == 0"),
        ("u8", "1 % x", "x == 0"),
        ("u32", "1 << x", "x == 32"),
        ("u8", "1 >> x", "x == 8"),
    ] {
        let p = Project::new(&format!("pub fn bad(x:{ty})->{ty} {{ {expression} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let cty = if ty == "u8" { "uint8" } else { "uint32" };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {cty} bad({cty} x) {{ requires {precondition}; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "accepted {expression} at {precondition}"
        );
    }
}

#[test]
fn rust_unsigned_nested_checks_and_short_circuit_preserve_panics() {
    for (expression, return_type, valid) in [
        ("(x + 1) as u8", "uint8", false),
        ("false && x + 1 > 0", "bool", true),
        ("true || x + 1 > 0", "bool", true),
        ("true && x + 1 > 0", "bool", false),
        ("false || x + 1 > 0", "bool", false),
    ] {
        let rust_type = if return_type == "bool" { "bool" } else { "u8" };
        let p = Project::new(&format!(
            "pub fn check(x:u32)->{rust_type} {{ {expression} }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; {return_type} check(uint32 x) {{ requires x == 4294967295u32; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        let result = C0VerificationSession::new_program_prepared(&sidecar, &prepared);
        assert_eq!(result.is_ok(), valid, "{expression}: {:?}", result.err());
    }
}

#[test]
fn rust_unsigned_casts_bitwise_and_assignments_verify() {
    let p = Project::new(
        "pub fn bits(mut x:u8)->u8 { x ^= 255; x &= 254; x |= 1; !x } pub fn narrow(x:i32)->u8 { x as u8 } pub fn signed(x:u32)->i32 { x as i32 } pub fn shift(x:u32, n:i32)->u32 { x >> n } pub fn byte_count(x:u32, n:u8)->u32 { x << n }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
uint8 bits(uint8 x) { requires x == 128; ensures result == 128; } by { execute(); simp(); }
uint8 narrow(int32 x) { requires x == -1; ensures result == 255; } by { execute(); simp(); }
int32 signed(uint32 x) { requires x == 4294967295u32; ensures result == -1; } by { execute(); simp(); }
uint32 shift(uint32 x, int32 n) { requires x == 4294967295u32; requires n == 31; ensures result == 1u32; } by { execute(); simp(); }
uint32 byte_count(uint32 x, uint8 n) { requires n < 32u32; ensures result == (x << (uint32)n); } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("n == 31", "n == -1"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_unsigned_references_and_byte_field_layout_verify() {
    let p = Project::new(
        "pub struct Pair { pub byte:u8, pub word:u32 } pub fn write(p:&mut u8, q:&mut u32) { *p = 255; *q = 4294967295; } pub fn field(p:&mut Pair) { p.byte = 7; }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
void write(uint8* p, uint32* q) { owns p[0..1]; owns q[0..1]; ensures p[0] == 255; ensures q[0] == 4294967295u32; } by { execute(); simp(); }
void field(struct Pair* p) { owns p->byte; owns p->word; ensures p->byte == 7; ensures p->word == old(p->word); } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

const SLICES_SOURCE: &str = include_str!("../examples/rust-slices/bytes.rs");
const SLICES_SIDECAR: &str = include_str!("../examples/rust-slices/bytes.click");

#[test]
fn rust_split_at_metadata_and_reads_verify() {
    let p = Project::new(include_str!("../examples/rust-split-at/split.rs"));
    let sidecar =
        include_str!("../examples/rust-split-at/split.click").replace("split.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(p.root.join("borrow.rs.click-rust.json")).unwrap())
            .unwrap();
    assert_eq!(artifact["schema"], 8);
    assert_eq!(artifact["functions"][0]["body"][0]["kind"], "slice_split");
    assert_eq!(artifact["functions"][0]["body"][0]["left"]["name"], "left");
    assert_eq!(
        artifact["functions"][0]["body"][0]["right"]["name"],
        "right"
    );
    for incorrect in [
        sidecar.replace("ensures result == mid;", "ensures result == 0u64;"),
        sidecar.replace(
            "ensures result == bytes_len - mid;",
            "ensures result == mid;",
        ),
        sidecar.replace(
            "ensures result == bytes[(int32)(uint32)mid];",
            "ensures result == bytes[0];",
        ),
        sidecar.replace("views bytes[0..(int32)(uint32)bytes_len];", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&incorrect, &prepared).is_err());
    }
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "left_length.contract",
        "right_length.contract",
        "left_first.contract",
        "right_first.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_split_at_endpoints_and_full_width_lengths_verify() {
    let p = Project::new(
        "pub fn length(bytes: &[u8], mid: usize) -> usize { let (left, right) = bytes.split_at(mid); right.len() }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for (length, midpoint) in [
        (0u64, 0u64),
        (4, 0),
        (4, 4),
        (2147483647, 2147483647),
        (4294967296, 1),
        (u64::MAX, 0),
    ] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint64 length(const uint8* bytes, uint64 bytes_len, uint64 mid) {{ requires bytes_len == {length}u64; requires mid == {midpoint}u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length - midpoint
        );
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    }
}

#[test]
fn rust_split_at_checks_bounds_before_pointer_narrowing() {
    let p = Project::new(
        "pub fn length(bytes: &[u8], mid: usize) -> usize { let (left, right) = bytes.split_at(mid); right.len() }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for (length, midpoint, label) in [
        (0u64, 1u64, "Rust split_at panic check"),
        (4, 5, "Rust split_at panic check"),
        (4, 4294967296, "Rust split_at panic check"),
        (
            u64::MAX,
            u64::MAX,
            "Rust split_at memory-model offset bound",
        ),
        (
            4294967296,
            4294967296,
            "Rust split_at memory-model offset bound",
        ),
    ] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint64 length(const uint8* bytes, uint64 bytes_len, uint64 mid) {{ requires bytes_len == {length}u64; requires mid == {midpoint}u64; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("invalid split must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        assert!(error.message().contains(label), "{}", error.message());
    }
}

#[test]
fn rust_split_at_rejects_unsupported_results_and_mutation() {
    for (source, message) in [
        (
            "pub fn bad(bytes: &[u8]) { let (left, right) = bytes.split_at(1); right[0] = 7; }",
            "cannot assign",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let (left, _) = bytes.split_at(1); }",
            "two plain tuple bindings",
        ),
        (
            "pub fn bad(bytes: &mut [u8]) { let (left, right) = bytes.split_at(1); }",
            "shared byte-slice local",
        ),
        (
            "pub fn bad(bytes: &[u8; 4]) { let (left, right) = bytes.split_at(1); }",
            "shared byte-slice local",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let pair = bytes.split_at(1); }",
            "two plain tuple bindings",
        ),
        (
            "pub fn bad(bytes: &mut [u8]) { let (left, right) = bytes.split_at_mut(1); }",
            "unsupported Rust type",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(message), "expected {message}: {error}");
        assert!(!p.root.join("borrow.rs.click-rust.json").exists());
    }
}

#[test]
fn rust_split_at_empty_results_reject_indexing() {
    for (length, midpoint, result_slice) in [
        (0u64, 0u64, "left"),
        (0, 0, "right"),
        (4, 0, "left"),
        (4, 4, "right"),
    ] {
        let p = Project::new(&format!(
            "pub fn read(bytes: &[u8], mid: usize) -> u8 {{ let (left, right) = bytes.split_at(mid); {result_slice}[0] }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint8 read(const uint8* bytes, uint64 bytes_len, uint64 mid) {{ requires bytes_len == {length}u64; requires mid == {midpoint}u64; views bytes[0..{length}]; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("empty result read must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        assert!(
            error.message().contains("Rust slice index panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_split_at_calls_nested_splits_aliases_and_argument_evaluation_verify() {
    let p = Project::new(
        r#"
pub fn first(bytes: &[u8]) -> u8 { bytes[0] }
pub fn nested(bytes: &[u8]) -> u8 {
    let (left, right) = bytes.split_at(1);
    let (prefix, suffix) = right.split_at(1);
    let alias = suffix;
    first(alias)
}
pub fn retarget(bytes: &[u8]) -> usize {
    let (mut left, right) = bytes.split_at(1);
    left = right;
    left.len()
}
pub fn shadow(bytes: &[u8]) -> usize {
    let (bytes, tail) = bytes.split_at(bytes.len() - 1);
    bytes.len()
}
pub fn next(counter: &mut u32) -> usize {
    let old = *counter;
    *counter += 1;
    old as usize
}
pub fn once(bytes: &[u8], counter: &mut u32) -> usize {
    let (left, right) = bytes.split_at(next(counter));
    right.len()
}
"#,
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = r#"verifying "borrow.rs";
uint8 first(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 2u64;
    views bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
uint8 nested(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 4u64;
    views bytes[0..4];
    ensures result == bytes[2];
    ensures bytes[0] == old(bytes[0]);
    ensures bytes[3] == old(bytes[3]);
} by { execute(); simp(); }
uint64 retarget(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 4u64;
    ensures result == 3u64;
} by { execute(); simp(); }
uint64 shadow(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 4u64;
    ensures result == 3u64;
} by { execute(); simp(); }
uint64 next(uint32* counter) {
    requires *counter == 1u32;
    owns counter[0..1];
    ensures result == 1u64;
    ensures *counter == 2u32;
} by { execute(); simp(); }
uint64 once(const uint8* bytes, uint64 bytes_len, uint32* counter) {
    requires bytes_len == 4u64;
    requires *counter == 1u32;
    owns counter[0..1];
    ensures result == 3u64;
    ensures *counter == 2u32;
} by { execute(); simp(); }
"#;
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures *counter == 2u32;", "ensures *counter == 3u32;"),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["expand", "--claim", "once.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_byte_slices_indexing_calls_and_expansion_verify() {
    let p = Project::new(SLICES_SOURCE);
    let sidecar = SLICES_SIDECAR.replace("bytes.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["audit"]);
    for claim in ["read.contract", "write.contract", "length.contract"] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_byte_slices_variable_length_indexing_verify() {
    let p = Project::new("pub fn read(bytes:&[u8], index:usize)->u8 { bytes[index] }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
uint8 read(const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    views bytes[0..(int32)bytes_len];
    ensures result == bytes[(int32)index];
} by { execute(); simp(); }";
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "read.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_byte_slices_reject_panics_and_missing_write_authority() {
    for (source, signature, resource, index) in [
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "uint8 bad(const uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            0u64,
        ),
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "uint8 bad(const uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            4,
        ),
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "uint8 bad(const uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            4294967296,
        ),
        (
            "pub fn bad(bytes:&mut [u8], index:usize) { bytes[index] = 7; }",
            "void bad(uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            1,
        ),
    ] {
        let p = Project::new(source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let length = if index == 0 { 0 } else { 4 };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ requires bytes_len == {length}u64; requires index == {index}u64; {resource} bytes[0..{length}]; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("unsafe slice contract must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        if resource == "views" && signature.starts_with("void") {
            assert!(error.message().contains("owns"), "{}", error.message());
        } else {
            assert!(
                error.message().contains("Rust slice index panic check"),
                "{}",
                error.message()
            );
        }
    }
}

#[test]
fn rust_byte_slices_length_preserves_target_width_and_index_borrows_verify() {
    let p = Project::new(
        "pub fn length(bytes:&[u8])->usize { bytes.len() } pub fn replace(bytes:&mut [u8], index:usize) { let child = &mut bytes[index]; *child = 9; } pub fn shift(x:u32, n:usize)->u32 { x << n }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
uint64 length(const uint8* bytes, uint64 bytes_len) { requires bytes_len == 4294967296u64; ensures result == 4294967296u64; } by { execute(); simp(); }
void replace(uint8* bytes, uint64 bytes_len, uint64 index) { requires bytes_len == 4u64; requires index < 4u64; owns bytes[0..4]; ensures bytes[(int32)index] == 9; } by { execute(); simp(); }
uint32 shift(uint32 x, uint64 n) { requires x == 1u32; requires n == 31u64; ensures result == 2147483648u32; } by { execute(); rewrite(n == 31u64); rewrite(x == 1u32); normalize(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    let error = C0VerificationSession::new_program_prepared(
        &sidecar.replace("n == 31u64", "n == 4294967296u64"),
        &prepared,
    )
    .err()
    .expect("oversized usize shift must fail before truncation");
    assert!(
        error.message().contains("Rust shl panic check"),
        "{}",
        error.message()
    );
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 4294967296u64", "ensures result == 0u64"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_byte_slice_unsupported_shapes_and_borrow_errors_are_refused() {
    for (source, message) in [
        (
            "pub fn bad(bytes:&mut [u8], index:usize) { bytes[index] += 1; }",
            "indexed compound assignments",
        ),
        (
            "pub fn bad(bytes:&[u8])->&[u8] { bytes }",
            "returns are not supported",
        ),
        (
            "pub fn bad(bytes:&[u32])->usize { bytes.len() }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(bytes:&mut [u8]) { let child = &mut *bytes; bytes[0] = 1; child[0] = 2; }",
            "cannot",
        ),
    ] {
        let p = Project::new(source);
        let result = refresh_import(&p.config());
        assert!(result.unwrap_err().contains(message), "{source}");
    }
}

#[test]
fn rust_fixed_array_references_indexing_and_reborrows_verify() {
    let p = Project::new(include_str!("../examples/rust-arrays/arrays.rs"));
    let sidecar =
        include_str!("../examples/rust-arrays/arrays.click").replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "read.contract",
        "write.contract",
        "signed.contract",
        "first.contract",
        "update.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures words[1] == 7u32", "ensures words[1] == 8u32"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_fixed_array_indices_reject_panics_before_narrowing() {
    for (length, index) in [(4, 4u64), (4, 4294967296), (0, 0), (4, u64::MAX)] {
        let p = Project::new(&format!(
            "pub fn read(bytes: &[u8; {length}], index: usize) -> u8 {{ bytes[index] }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint8 read(const uint8* bytes, uint64 index) {{ requires index == {index}u64; views bytes[0..{length}]; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("array index must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        assert!(
            error.message().contains("Rust array index panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_fixed_array_access_requires_memory_authority() {
    for (source, signature, resources) in [
        (
            "pub fn read(bytes: &[u8; 4]) -> u8 { bytes[0] }",
            "uint8 read(const uint8* bytes)",
            "",
        ),
        (
            "pub fn write(words: &mut [u32; 3]) { words[1] = 7; }",
            "void write(uint32* words)",
            "views words[0..3];",
        ),
    ] {
        let p = Project::new(source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ {resources} ensures 1 == 1; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("array access requires authority");
        assert_eq!(
            error.kind(),
            click::surface::ClickErrorKind::Proof,
            "{}",
            error.message()
        );
        assert!(
            error.message().contains(if resources.is_empty() {
                "views"
            } else {
                "owns"
            }),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_fixed_array_unsupported_shapes_and_conflicting_borrows_are_refused() {
    for (source, message) in [
        (
            "pub fn bad(bytes: &[u64; 4]) -> u64 { bytes[0] }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(words: &[u32; 536870912]) -> usize { words.len() }",
            "storage exceeds",
        ),
        (
            "pub fn bad(bytes: [u8; 4]) -> u8 { bytes[0] }",
            "by-value Rust arrays",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { bytes[0] += 1; }",
            "indexed compound assignments",
        ),
        (
            "pub fn bad(bytes: &[u8; 4]) -> &[u8] { bytes }",
            "reference/aggregate returns",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { let child = &mut bytes[0]; bytes[0] = 1; *child = 2; }",
            "cannot assign",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(message), "expected {message}: {error}");
        assert!(!p.root.join("borrow.rs.click-rust.json").exists());
    }
}

#[test]
fn rust_local_array_construction_and_whole_value_copies_verify() {
    let p = Project::new(include_str!("../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "literal.contract",
        "independent.contract",
        "replace.contract",
        "copy_into.contract",
        "repeat_call.contract",
        "zero_repeat_call.contract",
        "argument_order.contract",
        "assignment_order.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 8;", "ensures result == 16;"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_whole_array_copies_require_authority_for_every_element() {
    let p = Project::new(include_str!("../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for unsupported in [
        sidecar.replace("views source[0..2];", "views source[0..1];"),
        sidecar.replace("owns target[0..2];", "views target[0..2];"),
        sidecar.replace("owns target[0..2];", "owns target[0..1];"),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&unsupported, &prepared).is_err(),
            "unexpectedly verified: {unsupported}"
        );
    }
}

#[test]
fn rust_arrays_coerce_to_byte_slices_with_lengths_and_authority() {
    let p = Project::new(include_str!("../examples/rust-array-slices/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-slices/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "local.contract",
        "alias.contract",
        "retarget_mut.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    for incorrect in [
        sidecar.replace("ensures result == 4u64;", "ensures result == 1u64;"),
        sidecar.replace(
            "uint8 read(const uint8* bytes) {\n    views bytes[0..1];",
            "uint8 read(const uint8* bytes) {",
        ),
        sidecar.replace(
            "uint8 mutate(uint8* bytes) {\n    owns bytes[1..2];",
            "uint8 mutate(uint8* bytes) {\n    views bytes[1..2];",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&incorrect, &prepared).is_err());
    }
    let overflow = Project::new(
        &include_str!("../examples/rust-array-slices/arrays.rs")
            .replace("[3u8, 5, 9]", "[255u8, 5, 9]"),
    );
    refresh_import(&overflow.config()).unwrap();
    let overflow_prepared = load_import(&overflow.config()).unwrap();
    let error = C0VerificationSession::new_program_prepared(&sidecar, &overflow_prepared)
        .err()
        .expect("overflow must be rejected");
    assert!(
        error.message().contains("Rust add panic check"),
        "{}",
        error.message()
    );
}

#[test]
fn rust_array_to_slice_coercions_preserve_bounds_and_borrow_checks() {
    for (source, diagnostic) in [
        (
            "pub fn bad(bytes: &[u8; 4]) { let s: &mut [u8] = bytes; s[0] = 1; }",
            "mismatched types",
        ),
        (
            "pub fn bad(words: &[u32; 4]) -> usize { let s: &[u32] = words; s.len() }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { let s: &mut [u8] = bytes; bytes[0] = 1; s[0] = 2; }",
            "cannot assign",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
    }
    let p = Project::new(
        "pub fn read(bytes: &[u8; 2], index: usize) -> u8 { let s: &[u8] = bytes; s[index] }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for index in ["2u64", "4294967296u64", "18446744073709551615u64"] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint8 read(const uint8* bytes, uint64 index) {{ requires index == {index}; views bytes[0..2]; ensures result == 0; }} by {{ execute(); simp(); }}"
        );
        assert!(C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err());
    }
}

#[test]
fn rust_local_array_authority_and_copies_scale_with_array_length() {
    let mut samples = Vec::new();
    for length in [4, 16, 64] {
        let p = Project::new(&format!(
            "pub fn first(bytes: &[u8]) -> u8 {{ bytes[0] }} pub fn run() -> u8 {{ let bytes = [7u8; {length}]; let copied = bytes; first(&copied) }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = "verifying \"borrow.rs\"; uint8 first(const uint8* bytes, uint64 bytes_len) { requires bytes_len > 0u64; requires bytes_len <= 2147483647u64; views bytes[0..1]; ensures result == bytes[0]; } by { execute(); simp(); } uint8 run() { ensures result == 7; } by { execute(); simp(); }";
        let (result, work) = click::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(sidecar, &prepared)
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 8,
            "array verification grew faster than its explicit operations: {samples:?}"
        );
    }
}

#[test]
fn rust_array_to_slice_calls_preserve_untouched_local_elements() {
    let p = Project::new(
        "pub fn first(bytes: &[u8]) -> u8 { bytes[0] } pub fn set(bytes: &mut [u8]) { bytes[1] = 7; } pub fn untouched() -> u8 { let mut bytes = [3u8, 5, 9]; set(&mut bytes); bytes[0] } pub fn initial() -> u8 { let bytes = [3u8, 5, 9]; first(&bytes) }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; uint8 first(const uint8* bytes, uint64 bytes_len) { requires bytes_len > 0u64; requires bytes_len <= 2147483647u64; views bytes[0..1]; ensures result == bytes[0]; } by { execute(); simp(); } void set(uint8* bytes, uint64 bytes_len) { requires bytes_len > 1u64; requires bytes_len <= 2147483647u64; owns bytes[1..2]; ensures bytes[1] == 7; } by { execute(); simp(); } uint8 untouched() { ensures result == 3; } by { execute(); simp(); } uint8 initial() { ensures result == 3; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

const USIZE_SOURCE: &str = include_str!("../examples/rust-usize/arithmetic.rs");
const USIZE_SIDECAR: &str = include_str!("../examples/rust-usize/arithmetic.click");

#[test]
fn rust_usize_arithmetic_casts_and_expansion_verify() {
    let p = Project::new(USIZE_SOURCE);
    let sidecar = USIZE_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let general_mul = sidecar.replace(
        "requires x == 4294967296u64;\n    requires y == 2147483648u64;\n    ensures result == 9223372036854775808u64;",
        "requires y != 0u64;\n    requires x <= 18446744073709551615u64 / y;\n    ensures result == x * y;",
    );
    assert_ne!(general_mul, sidecar);
    C0VerificationSession::new_program_prepared(&general_mul, &prepared).unwrap();
    for changed in [
        sidecar.replace("requires index == 0u64;", "requires index == 1u64;"),
        sidecar.replace(
            "requires index == 0u64;",
            "requires index == 18446744073709551615u64;",
        ),
        sidecar.replace(
            "requires bytes_len <= 18446744073709551614u64;",
            "requires bytes_len == 18446744073709551615u64;",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&changed, &prepared).is_err());
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace(
                "ensures result == 9223372036854775808u64;",
                "ensures result == 0u64;"
            ),
            &prepared,
        )
        .is_err()
    );
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "add.contract",
        "mul.contract",
        "right.contract",
        "computed.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_usize_panic_paths_are_rejected() {
    for (expression, precondition) in [
        ("x + 1", "x == 18446744073709551615u64"),
        ("x - 1", "x == 0u64"),
        ("x * 2", "x == 9223372036854775808u64"),
        ("1 / x", "x == 0u64"),
        ("1 % x", "x == 0u64"),
        ("1 << x", "x == 64u64"),
        ("1 >> x", "x == 4294967296u64"),
        ("1 << x", "x == 18446744073709551615u64"),
    ] {
        let p = Project::new(&format!("pub fn bad(x:usize)->usize {{ {expression} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint64 bad(uint64 x) {{ requires {precondition}; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "accepted {expression} at {precondition}"
        );
    }
}

#[test]
fn rust_usize_boundaries_and_nested_checks() {
    for (source, return_type, precondition, expected, valid) in [
        (
            "x + 0",
            "uint64",
            "x == 18446744073709551615u64",
            "18446744073709551615u64",
            true,
        ),
        (
            "x * 0",
            "uint64",
            "x == 18446744073709551615u64",
            "0u64",
            true,
        ),
        (
            "x * 1",
            "uint64",
            "x == 18446744073709551615u64",
            "18446744073709551615u64",
            true,
        ),
        (
            "x - 1",
            "uint64",
            "x == 9223372036854775808u64",
            "9223372036854775807u64",
            true,
        ),
        (
            "x / 2",
            "uint64",
            "x == 18446744073709551615u64",
            "9223372036854775807u64",
            true,
        ),
        (
            "x % 2",
            "uint64",
            "x == 18446744073709551615u64",
            "1u64",
            true,
        ),
        (
            "{ let mut y = x; y += 1; y -= 1; y *= 1; y /= 1; y %= 2; y <<= 63; y >>= 63; y }",
            "uint64",
            "x == 4294967297u64",
            "1u64",
            true,
        ),
        (
            "(x + 1) as u32",
            "uint32",
            "x == 18446744073709551615u64",
            "0u32",
            false,
        ),
        (
            "false && x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "0",
            true,
        ),
        (
            "true || x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "1",
            true,
        ),
        (
            "true && x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "1",
            false,
        ),
    ] {
        let ty = match return_type {
            "uint32" => "u32",
            "bool" => "bool",
            _ => "usize",
        };
        let p = Project::new(&format!("pub fn check(x:usize)->{ty} {{ {source} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; {return_type} check(uint64 x) {{ requires {precondition}; ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        let result = C0VerificationSession::new_program_prepared(&sidecar, &prepared);
        assert_eq!(result.is_ok(), valid, "{source}: {:?}", result.err());
    }
    let p = Project::new("pub fn right(x:usize, n:i32)->usize { x >> n }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; uint64 right(uint64 x, int32 n) { requires n == -1; ensures result == result; } by { execute(); simp(); }";
    assert!(C0VerificationSession::new_program_prepared(sidecar, &prepared).is_err());
}

#[test]
fn rust_while_loop_invariants_verify_and_expand() {
    let p = Project::new(include_str!("../examples/rust-loops/loops.rs"));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-loops/loops.click").replace("loops.rs", "borrow.rs");
    let (_, verified) = C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 3);
    for false_claim in [
        sidecar.replace("ensures result == n;", "ensures result == n + 1;"),
        sidecar.replace("invariant i <= bytes_len;", "invariant i < bytes_len;"),
        sidecar.replace("decreases bytes_len - i;", "decreases i;"),
        sidecar.replace("requires value == 1;", "requires value == 2147483647;"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&false_claim, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in ["count.contract", "accumulate.contract", "walk.contract"] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_while_loop_rejects_unsupported_control_flow_and_guards() {
    for (source, diagnostic) in [
        ("pub fn bad() { for _i in 0..2 {} }", "Rust for loops"),
        (
            "pub fn bad() { 'outer: while true {} }",
            "unlabeled Rust while",
        ),
        (
            "pub fn bad() { while true { break; } }",
            "break and continue",
        ),
        (
            "pub fn bad() { while true { continue; } }",
            "break and continue",
        ),
        (
            "pub fn bad(mut i:i32, n:i32) { while i + 1 < n { i += 1; } }",
            "Rust while conditions",
        ),
        (
            "fn guard()->bool { false } pub fn bad() { while guard() {} }",
            "Rust while conditions",
        ),
        (
            "pub fn bad(bytes:&[u8]) { while bytes[0] != 0 {} }",
            "Rust while conditions",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
    }
}

#[test]
fn rust_while_loop_panic_paths_are_rejected() {
    for (source, signature, invariant) in [
        (
            "pub fn bad(mut i:i32) { while i >= 0 { i += 1; } }",
            "void bad(int32 i)",
            "i >= 0",
        ),
        (
            "pub fn bad(mut i:usize) { while i <= 18446744073709551615usize { i += 1; } }",
            "void bad(uint64 i)",
            "i <= 18446744073709551615u64",
        ),
        (
            "pub fn bad(bytes:&[u8]) { let mut i=0usize; while i <= bytes.len() { let _byte=bytes[i]; i += 1; } }",
            "void bad(const uint8* bytes, uint64 bytes_len)",
            "i <= bytes_len",
        ),
    ] {
        let p = Project::new(source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let prefix = if signature.contains("bytes") {
            "execute_until(statement(4));"
        } else {
            "step();"
        };
        let requirements = if signature.contains("bytes") {
            "requires bytes_len <= 2147483647u64; views bytes[0..(int32)bytes_len];"
        } else {
            "step();"
        };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ {requirements} }} by {{ {prefix} loop {{ invariant {invariant}; }} execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("panic path must be rejected");
        assert!(
            !error.message().contains("requires the execution frontier"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_nested_while_loop_invariants_keep_preorder_indices() {
    let p = Project::new(
        "pub fn nested()->i32 { let mut i=0; while i < 1 { let mut j=0; while j < 1 { j += 1; } i += 1; } i }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; int32 nested() { ensures result == 1; } by { execute_until(statement(4)); loop { decreases 1-i; invariant 0<=i and i<=1; preserve by { execute_until(statement(9)); loop { decreases 1-j; invariant 0<=j and j<=1; } execute_until(statement(24)); step(); close_invariants(); } } execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["expand", "--claim", "nested.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_readable_local_names_preserve_shadowed_binding_identities() {
    let p = Project::new(
        "pub fn run(n:i32)->i32 { let n=2; let n=n+1; let __rust_checked_0=n+1; __rust_checked_0 }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; int32 run(int32 n) { ensures result == 4; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result == 4", "result == 3"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_byte_sum_proves_exact_prefix_sum_and_expands() {
    let p = Project::new(include_str!("../examples/rust-byte-sum/sum.rs"));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-byte-sum/sum.click").replace("sum.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace(
            "ensures to_integer(result) == old(prefix",
            "ensures to_integer(result) + 1 == old(prefix",
        ),
        sidecar.replace("invariant i <= bytes_len;", "invariant i < bytes_len;"),
        sidecar.replace(
            "invariant to_integer(total) == prefix(bytes, (int32)(uint32)i);",
            "invariant to_integer(total) + 1 == prefix(bytes, (int32)(uint32)i);",
        ),
        sidecar.replace("decreases bytes_len - i;", "decreases i;"),
        sidecar.replace("requires bytes_len <= 1000u64;", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

fn assert_slice_iterator_artifact(p: &Project, by_reference: bool) {
    let bytes = fs::read(p.root.join("borrow.rs.click-rust.json")).unwrap();
    let artifact: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(artifact["schema"], 8);
    let iterator = &artifact["functions"][0]["body"][1];
    assert_eq!(iterator["kind"], "slice_for");
    assert_eq!(iterator["iterator"], "__rust_iter_3_5");
    assert_eq!(iterator["by_reference"], by_reference);
    assert_eq!(iterator["slice"]["name"], "bytes");
    assert_eq!(iterator["binding"]["name"], "byte");
    assert_eq!(iterator["body"].as_array().unwrap().len(), 1);
    assert_eq!(iterator["body"][0]["target"]["name"], "total");
    // The typed operation retains the source body, with no invented progress
    // declaration, checked index expression, or post-body counter increment.
    let text = String::from_utf8(bytes).unwrap();
    assert!(!text.contains("__rust_iter_index"));
    assert!(!text.contains("\"kind\":\"usize\""));
    assert!(!text.contains("\"kind\":\"index\""));
}

#[test]
fn rust_empty_slice_iterator_needs_no_read_authority() {
    for expression in ["bytes", "bytes.iter()"] {
        let source = format!(
            "pub fn empty(bytes: &[u8]) -> i32 {{ for byte in {expression} {{ let _value = *byte; }} 0 }}"
        );
        let p = Project::new(&source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = "verifying \"borrow.rs\"; int32 empty(const uint8* bytes, uint64 bytes_len) { requires bytes_len == 0u64; ensures result == 0; } by { execute_until(statement(6)); loop { invariant __rust_iter_1_37_remaining == 0; decreases __rust_iter_1_37_remaining; preserve by { execute(); close_invariants(); } } execute(); simp(); }";
        C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
        assert!(
            C0VerificationSession::new_program_prepared(
                &sidecar.replace("bytes_len == 0u64", "bytes_len == 1u64"),
                &prepared
            )
            .is_err()
        );
    }
}

#[test]
fn rust_slice_for_sum_verifies_and_expands() {
    let p = Project::new(include_str!("../examples/rust-iterators/sum.rs"));
    refresh_import(&p.config()).unwrap();
    assert_slice_iterator_artifact(&p, false);
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-iterators/sum.click").replace("sum.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let copied_iter = Project::new(
        &include_str!("../examples/rust-iterators/sum.rs")
            .replace("in bytes {", "in bytes.iter() {"),
    );
    refresh_import(&copied_iter.config()).unwrap();
    let copied_prepared = load_import(&copied_iter.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &copied_prepared).unwrap();
    for invalid in [
        sidecar.replace(
            "ensures to_integer(result) == old(prefix",
            "ensures to_integer(result) + 1 == old(prefix",
        ),
        sidecar.replace(
            "decreases __rust_iter_3_5_remaining;",
            "decreases -__rust_iter_3_5_remaining;",
        ),
        sidecar.replace(
            "invariant 0 <= __rust_iter_3_5_remaining and __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len;",
            "invariant 0 <= __rust_iter_3_5_remaining and __rust_iter_3_5_remaining < (int32)(uint32)bytes_len;",
        ),
        sidecar.replace(
            "invariant __rust_iter_3_5_cursor == bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining);",
            "invariant __rust_iter_3_5_cursor == bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining + 1);",
        ),
        sidecar.replace("requires bytes_len <= 1000u64;", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_slice_for_rejects_unsupported_iteration() {
    for source in [
        "pub fn bad(bytes: &[u8]) { for byte in bytes.iter().rev() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes.iter_mut() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes.iter() {} }",
        "pub fn bad(bytes: &[u8]) { let iter = bytes.iter(); for byte in iter {} }",
        "pub fn bad(mut bytes: &[u8]) { for byte in bytes.iter() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes {} }",
        "pub fn bad(mut bytes: &[u8]) { for &byte in bytes {} }",
        "pub fn bad(bytes: &[u8]) { 'outer: for &byte in bytes {} }",
        "pub fn bad(bytes: &[u8]) { for &byte in bytes { break; } }",
        "pub fn bad(bytes: &[u8]) { for &byte in bytes { continue; } }",
        "pub fn bad(bytes: &[u8; 2]) { for &byte in bytes {} }",
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(
            error.contains("Rust for loops")
                || error.contains("break and continue")
                || error.contains("unsupported Rust type `std::slice::Iter"),
            "{error}"
        );
        assert!(!error.contains("panicked"), "{error}");
    }
}

#[test]
fn rust_slice_iter_reference_sum_verifies_and_expands() {
    let source = include_str!("../examples/rust-iter-references/sum.rs");
    let sidecar =
        include_str!("../examples/rust-iter-references/sum.click").replace("sum.rs", "borrow.rs");
    // Shared references from both the implicit slice iterator and .iter()
    // have the same checked address and dereference semantics.
    for source in [source.to_string(), source.replace("bytes.iter()", "bytes")] {
        let p = Project::new(&source);
        refresh_import(&p.config()).unwrap();
        assert_slice_iterator_artifact(&p, true);
        let prepared = load_import(&p.config()).unwrap();
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
        for invalid in [
            sidecar.replace(
                "ensures to_integer(result) == old(prefix",
                "ensures to_integer(result) + 1 == old(prefix",
            ),
            sidecar.replace("requires bytes_len <= 1000u64;", ""),
            sidecar.replace("views bytes[0..(int32)(uint32)bytes_len];", ""),
            sidecar.replace(
                "decreases __rust_iter_3_5_remaining;",
                "decreases -__rust_iter_3_5_remaining;",
            ),
        ] {
            assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
        }
        if source.contains(".iter()") {
            fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
            assert_cli(&p, &["profile"]);
            assert_cli(&p, &["audit"]);
            assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
            assert_cli(&p, &["verify"]);
        }
    }
    let p = Project::new("pub fn bad(bytes: &[u8]) { for byte in bytes.iter() { *byte = 0; } }");
    let error = refresh_import(&p.config()).unwrap_err();
    assert!(error.contains("cannot assign"), "{error}");
}

#[test]
fn rust_chunks_exact_remainder_metadata_and_bytes() {
    let source = "pub fn tail_len(bytes: &[u8], size: usize) -> usize { let chunks = bytes.chunks_exact(size); let tail = chunks.remainder(); tail.len() }
    pub fn tail_byte(bytes: &[u8]) -> u8 { let chunks = bytes.chunks_exact(2); let tail = chunks.remainder(); tail[0] }";
    let p = Project::new(source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
    uint64 tail_len(const uint8* bytes, uint64 bytes_len, uint64 size) {
        requires bytes_len <= 2147483647u64; requires size != 0u64;
        ensures result == bytes_len % size;
    } by { execute(); simp(); }
    uint8 tail_byte(const uint8* bytes, uint64 bytes_len) {
        requires bytes_len == 5u64; views bytes[0..5];
        ensures result == bytes[4];
    } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace("requires size != 0u64;", ""),
        sidecar.replace("requires bytes_len <= 2147483647u64;", ""),
        sidecar.replace("views bytes[0..5];", ""),
        sidecar.replace("result == bytes[4]", "result == bytes[3]"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}

#[test]
fn rust_chunks_exact_loops_cover_input_and_preserve_bytes() {
    let source = include_str!("../examples/rust-chunks-exact/chunks.rs");
    let sidecar = include_str!("../examples/rust-chunks-exact/chunks.click")
        .replace("chunks.rs", "borrow.rs");
    for source in [
        source.to_string(),
        source
            .replace("let chunks =", "let mut chunks =")
            .replace("in chunks {", "in &mut chunks {")
            .replace("tail.len()", "chunks.remainder().len()"),
    ] {
        let p = Project::new(&source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .unwrap_or_else(|error| panic!("{}", error.message()));
        for invalid in [
            sidecar.replace(
                "ensures result == bytes_len % 4u64;",
                "ensures result == bytes_len % 4u64 + 1u64;",
            ),
            sidecar.replace("views bytes[0..(int32)(uint32)bytes_len];", ""),
            sidecar.replace("requires bytes_len <= 1000u64;", ""),
            sidecar.replace(
                "invariant chunks_remaining % 4 == 0;",
                "invariant chunks_remaining % 4 == 1;",
            ),
            sidecar.replace("bytes[k] == old(bytes[k])", "bytes[k] != old(bytes[k])"),
        ] {
            assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
        }
        fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
        assert_cli(&p, &["profile"]);
        assert_cli(&p, &["audit"]);
        assert_cli(&p, &["expand", "--claim", "cover.contract", "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_chunks_exact_boundaries_and_full_width_sizes() {
    let p = Project::new(
        "pub fn length(bytes: &[u8], size: usize) -> usize { let chunks = bytes.chunks_exact(size); chunks.remainder().len() }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for (length, size) in [
        (0u64, 4u64),
        (8, 4),
        (5, 4),
        (3, 4),
        (5, 1),
        (5, 4294967296),
        (5, 9223372036854775808),
        (5, u64::MAX),
    ] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint64 length(const uint8* bytes, uint64 bytes_len, uint64 size) {{ requires bytes_len == {length}u64; requires size == {size}u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length % size
        );
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    }
    for length in [0, 5] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint64 length(const uint8* bytes, uint64 bytes_len, uint64 size) {{ requires bytes_len == {length}u64; requires size == 0u64; ensures result == 0u64; }} by {{ execute(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("zero size must fail");
        assert!(
            error
                .message()
                .contains("Rust chunks_exact zero size panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_chunks_exact_evaluates_size_once_and_keeps_shadowed_iterators_distinct() {
    let p = Project::new("pub fn size(p: &mut i32) -> usize { *p = *p + 1; 4 }
    pub fn length(bytes: &[u8], p: &mut i32) -> usize { let chunks = bytes.chunks_exact(size(p)); chunks.remainder().len() }
    pub fn shadow(bytes: &[u8]) -> usize { let chunks = bytes.chunks_exact(4); let tail = chunks.remainder(); let chunks = tail.chunks_exact(1); chunks.remainder().len() }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
    uint64 size(int32* p) { requires p[0] == 0; owns p[0..1]; ensures p[0] == 1; ensures result == 4u64; } by { execute(); simp(); }
    uint64 length(const uint8* bytes, uint64 bytes_len, int32* p) { requires bytes_len == 5u64; requires p[0] == 0; owns p[0..1]; ensures p[0] == 1; ensures result == 1u64; } by { execute(); simp(); }
    uint64 shadow(const uint8* bytes, uint64 bytes_len) { requires bytes_len == 5u64; ensures result == 0u64; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    let artifact = prepared.export();
    assert!(matches!(
        &artifact.functions[1].body[0],
        click::languages::rust::schema::Statement::ChunkDeclare {
            size: click::languages::rust::schema::Expression::Call { .. },
            ..
        }
    ));
}

#[test]
fn rust_chunks_exact_rejects_writes_and_unsupported_iterator_protocols() {
    for (source, diagnostic) in [
        (
            "pub fn bad(bytes: &[u8]) { for chunk in bytes.chunks_exact(4) { chunk[0] = 0; } }",
            "cannot assign",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let chunks = bytes.chunks_exact(4); let tail = chunks.remainder(); tail[0] = 0; }",
            "cannot assign",
        ),
        (
            "pub fn bad(bytes: &mut [u8]) { let chunks = bytes.chunks_exact_mut(4); }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(bytes: &[u8]) { for chunk in bytes.chunks_exact(4).rev() {} }",
            "Rust for loops",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let chunks = bytes.chunks_exact(4); let copy = chunks; }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let mut chunks = bytes.chunks_exact(4); let item = chunks.next(); }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let chunks = bytes.chunks_exact(4); for chunk in chunks {} chunks.remainder(); }",
            "moved value",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!error.contains("panicked"), "{error}");
    }
}

#[test]
fn rust_chunks_exact_direct_nested_loops_keep_independent_state() {
    let source = "pub fn nested(bytes: &[u8]) -> usize {
    for chunk in bytes.chunks_exact(4) {
        for part in chunk.chunks_exact(2) {}
    }
    0
}";
    let p = Project::new(source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
    uint64 nested(const uint8* bytes, uint64 bytes_len) {
        requires bytes_len == 8u64; ensures result == 0u64;
    } by {
        execute_until(statement(18));
        loop {
            decreases __rust_iter_2_5_remaining;
            invariant __rust_iter_2_5_size == 4u64;
            invariant 0 <= __rust_iter_2_5_remaining and __rust_iter_2_5_remaining <= 8;
            preserve by {
                execute_until(statement(44));
                loop {
                    decreases __rust_iter_3_9_remaining;
                    invariant __rust_iter_3_9_size == 2u64;
                    invariant 0 <= __rust_iter_3_9_remaining and __rust_iter_3_9_remaining <= 4;
                    preserve by { execute_until(statement(52)); step(); close_invariants(); }
                }
                close_invariants();
            }
        }
        execute(); simp();
    }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["expand", "--claim", "nested.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_integer_from_preserves_native_unsigned_values() {
    let p = Project::new(
        "pub fn byte(x: u8) -> u32 { u32::from(x) }
        pub fn half(x: u8) -> u16 { u16::from(x) }
        pub fn word(x: u16) -> u32 { <u32 as From<u16>>::from(x) }
        pub fn size(x: u16) -> usize { usize::from(x) }
        pub fn identity(x: u16) -> u16 { u16::from(x) }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        uint32 byte(uint8 x) { ensures result == (uint32)x; } by { execute(); simp(); }
        uint16 half(uint8 x) { ensures ((uint32)result) == (uint32)x; } by { execute(); simp(); }
        uint32 word(uint16 x) { ensures result == (uint32)x; } by { execute(); simp(); }
        uint64 size(uint16 x) { ensures result == (uint64)x; } by { execute(); simp(); }
        uint16 identity(uint16 x) { ensures result == x; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result == (uint32)x", "result == (uint32)x + 1u32"),
            &prepared,
        )
        .is_err()
    );
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "word.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_integer_from_evaluates_nested_calls_once_in_order() {
    let p = Project::new(
        "pub fn next(p: &mut i32) -> u8 { *p += 1; *p as u8 }
        pub fn pair(p: &mut i32) -> u32 { u32::from(next(p)) * 256 + u32::from(next(p)) }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        uint8 next(int32* p) { requires 0 <= p[0] and p[0] <= 1; owns p[0..1];
            ensures p[0] == old(p[0]) + 1; ensures ((uint32)result) == ((uint32)p[0] & 255u32);
        } by { execute(); simp(); }
        uint32 pair(int32* p) { requires p[0] == 0; owns p[0..1];
            ensures p[0] == 2; ensures result == 258u32;
        } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

#[test]
fn rust_u16_casts_truncate_and_shifts_keep_sixteen_bits() {
    let p = Project::new(
        "pub fn low(x: usize) -> u16 { x as u16 }
        pub fn signed(x: i32) -> u16 { x as u16 }
        pub fn byte(x: u16) -> u8 { x as u8 }
        pub fn invert(x: u16) -> u16 { !x }
        pub fn shift(x: u16, count: usize) -> u16 { x << count }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        uint16 low(uint64 x) { ensures ((uint32)result) == ((uint32)x & 65535u32); } by { execute(); simp(); }
        uint16 signed(int32 x) { ensures ((uint32)result) == ((uint32)x & 65535u32); } by { execute(); simp(); }
        uint8 byte(uint16 x) { ensures ((uint32)result) == ((uint32)x & 255u32); } by { execute(); simp(); }
        uint16 invert(uint16 x) { ensures ((uint32)result) == (~(uint32)x & 65535u32); } by { execute(); simp(); }
        uint16 shift(uint16 x, uint64 count) { requires count < 16u64;
            ensures ((uint32)result) == (((uint32)x << (uint32)count) & 65535u32);
        } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for count in [16, 4294967296u64, u64::MAX] {
        let invalid = sidecar.replace(
            "requires count < 16u64;",
            &format!("requires count == {count}u64;"),
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap();
        assert!(
            error.message().contains("Rust shl panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_u16_arithmetic_checks_its_own_width() {
    let p = Project::new(
        "pub fn add(x: u16) -> u16 { x + 1 }
        pub fn sub(x: u16) -> u16 { x - 1 }
        pub fn mul(x: u16) -> u16 { x * 3 }
        pub fn div(x: u16, d: u16) -> u16 { x / d }
        pub fn rem(x: u16, d: u16) -> u16 { x % d }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        uint16 add(uint16 x) { requires x <= 65534; ensures ((uint32)result) == (uint32)x + 1u32; } by { execute(); simp(); }
        uint16 sub(uint16 x) { requires 1 <= x; ensures ((uint32)result) == (uint32)x - 1u32; } by { execute(); simp(); }
        uint16 mul(uint16 x) { requires x <= 21845; ensures ((uint32)result) == (uint32)x * 3u32; } by { have 0 <= ((int32)x) * 3 by { arithmetic() using { 0 <= x; x <= 21845; } } have ((int32)x) * 3 <= 65535 by { arithmetic() using { 0 <= x; x <= 21845; } } execute(); simp(); }
        uint16 div(uint16 x, uint16 d) { requires 0 < d; ensures ((uint32)result) == (uint32)x / (uint32)d; } by { execute(); simp(); }
        uint16 rem(uint16 x, uint16 d) { requires 0 < d; ensures ((uint32)result) == (uint32)x % (uint32)d; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for (operator, input, divisor, label) in [
        ("+", 65535, 1, "Rust add panic check"),
        ("-", 0, 1, "Rust sub panic check"),
        ("*", 21846, 3, "Rust mul panic check"),
        ("/", 5, 0, "division by zero"),
        ("%", 5, 0, "division by zero"),
    ] {
        let p = Project::new(&format!(
            "pub fn bad(x: u16, d: u16) -> u16 {{ x {operator} d }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint16 bad(uint16 x, uint16 d) {{ requires x == {input}; requires d == {divisor}; ensures result == 0; }} by {{ execute(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .unwrap();
        assert!(error.message().contains(label), "{}", error.message());
    }
}

#[test]
fn rust_integer_from_rejects_other_conversions_and_shadowed_methods() {
    for (source, diagnostic) in [
        (
            "pub fn bad(x: bool) -> u8 { u8::from(x) }",
            "only lossless supported unsigned",
        ),
        ("pub fn bad(x: u32) -> u16 { u16::from(x) }", "From<u32>"),
        (
            "pub fn bad(x: u8) -> u64 { u64::from(x) }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(x: u8) -> u32 { x.into() }",
            "only builtin byte-slice",
        ),
        (
            "pub struct Word { x: u32 } impl Word { pub fn from(x: u8) -> u32 { 99 } } pub fn bad(x: u8) -> u32 { Word::from(x) }",
            "Rust source boundary",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!error.contains("panicked"), "{error}");
    }
}

#[test]
fn rust_u16_accumulator_fields_and_references_preserve_authority() {
    let p = Project::new(include_str!(
        "../examples/rust-integer-conversions/accumulator.rs"
    ));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = include_str!("../examples/rust-integer-conversions/accumulator.click")
        .replace("accumulator.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace("ensures state->a == 254;", "ensures state->a == 255;"),
        sidecar.replace("owns state->a;", "views state->a;"),
        sidecar.replace("owns state->b;", ""),
        sidecar.replace("views value[0..1];", ""),
        sidecar.replace(
            "ensures state->b == old(state->b);",
            "ensures state->b != old(state->b);",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "bump_a.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}
