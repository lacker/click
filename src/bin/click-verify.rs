use std::env;
use std::fs;
use std::path::Path;

use click::cli::{parse_source_location, read_verifying_sources, source_refs};
use click::lang::click::verify_c0_sources_at;

const USAGE: &str = "usage: click-verify <sidecar.click>:<line>:<column>";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-verify: {message}");
        std::process::exit(1);
    }
}

fn entry() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let [location] = arguments.as_slice() else {
        return Err(USAGE.to_string());
    };
    let (click_path, line, column) = parse_source_location(location)?;
    verify_location(&click_path, line, column)
}

fn verify_location(click_path: &Path, line: usize, column: usize) -> Result<(), String> {
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let sources = read_verifying_sources(click_path, &click_source)?;
    verify_c0_sources_at(&click_source, &source_refs(&sources), line, column)
        .map_err(|error| error.message().to_string())?;
    Ok(())
}
