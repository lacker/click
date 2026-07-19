use std::fs;
use std::path::{Path, PathBuf};

use click::lang::click::verify_c0_sources;

#[test]
fn example_projects() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let examples_dir = manifest_dir.join("examples");
    let requested = std::env::var_os("CLICK_EXAMPLE");
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

    assert!(
        !projects.is_empty(),
        "expected at least one matching example project in `{}`",
        examples_dir.display(),
    );

    for project in projects {
        run_example_project(&project);
    }
}

fn run_example_project(project: &Path) {
    let mut c_paths = files_with_extension(project, "c");
    let mut click_paths = files_with_extension(project, "click");

    assert!(
        !click_paths.is_empty(),
        "example project `{}` must contain at least one .click sidecar",
        project.display()
    );

    c_paths.sort();
    click_paths.sort();

    let c_sources = c_paths
        .iter()
        .map(|path| {
            let filename = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_else(|| panic!("invalid UTF-8 path `{}`", path.display()))
                .to_string();
            let source = fs::read_to_string(path)
                .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
            (filename, source)
        })
        .collect::<Vec<_>>();
    let c_source_refs = c_sources
        .iter()
        .map(|(filename, source)| (filename.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", click_path.display()));
        verify_c0_sources(&click_source, &c_source_refs).unwrap_or_else(|error| {
            panic!(
                "example sidecar `{}` failed: {}",
                click_path.display(),
                error.message()
            )
        });
    }
}

fn files_with_extension(directory: &Path, extension: &str) -> Vec<PathBuf> {
    fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", directory.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("failed to read directory entry: {error}"))
                .path()
        })
        .filter(|path| path.extension().is_some_and(|actual| actual == extension))
        .collect()
}
