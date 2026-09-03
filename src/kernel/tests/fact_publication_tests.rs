use std::fs;
use std::path::{Path, PathBuf};

fn rust_sources_under(root: &Path, sources: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).expect("source directory should be readable") {
        let path = entry
            .expect("source directory entry should be readable")
            .path();
        if path.is_dir() {
            rust_sources_under(&path, sources);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            sources.push(path);
        }
    }
}

#[test]
fn raw_proof_fact_publication_stays_inside_the_kernel() {
    let source_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let kernel_root = source_root.join("kernel");
    let facts_source = fs::read_to_string(kernel_root.join("proof/facts.rs"))
        .expect("proof fact implementation should be readable");
    let object_source = fs::read_to_string(kernel_root.join("proof/object.rs"))
        .expect("proof object implementation should be readable");
    assert!(facts_source.contains("pub(in crate::kernel) fn with_fact"));
    assert!(object_source.contains("pub(in crate::kernel) fn publish_checked_focused_result"));

    let mut sources = Vec::new();
    rust_sources_under(&source_root, &mut sources);
    for path in sources {
        if path.starts_with(&kernel_root) {
            continue;
        }
        let source = fs::read_to_string(&path).expect("Rust source should be readable");
        assert!(
            !source.contains(".with_fact("),
            "raw ProofFacts::with_fact caller escaped the kernel: {}",
            path.display()
        );
        assert!(
            !source.contains("publish_checked_focused_result("),
            "raw focused proof publication caller escaped the kernel: {}",
            path.display()
        );
    }
}
