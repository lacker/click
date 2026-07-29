use std::env;
use std::fs;
use std::path::Path;

use click::cli::{
    looks_like_source_location, parse_source_location, read_verifying_sources, source_refs,
};
use click::lang::click::{verify_c0_sources, verify_c0_sources_at};

const USAGE: &str = "\
usage: click-verify <sidecar.click>[:<line>:<column>]

Verifies the whole sidecar, or, when a one-based :LINE:COLUMN suffix is
supplied, only the proof unit containing that source location and the C
functions it calls.";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-verify: {message}");
        std::process::exit(1);
    }
}

fn entry() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if matches!(arguments.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let [argument] = arguments.as_slice() else {
        return Err(USAGE.to_string());
    };
    if looks_like_source_location(argument) {
        let (click_path, line, column) = parse_source_location(argument)?;
        verify_location(&click_path, line, column)
    } else {
        verify_file(Path::new(argument))
    }
}

fn verify_file(click_path: &Path) -> Result<(), String> {
    let (click_source, sources) = load_sidecar(click_path)?;
    verify_c0_sources(&click_source, &source_refs(&sources))
        .map_err(|error| error.message().to_string())?;
    Ok(())
}

fn verify_location(click_path: &Path, line: usize, column: usize) -> Result<(), String> {
    let (click_source, sources) = load_sidecar(click_path)?;
    verify_c0_sources_at(&click_source, &source_refs(&sources), line, column)
        .map_err(|error| error.message().to_string())?;
    Ok(())
}

fn load_sidecar(click_path: &Path) -> Result<(String, Vec<(String, String)>), String> {
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let sources = read_verifying_sources(click_path, &click_source)?;
    Ok((click_source, sources))
}
