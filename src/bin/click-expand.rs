use std::env;
use std::fs;
use std::path::PathBuf;

use click::lang::click::{CProofClaim, expand_c0_claim_source, verifying_source_paths};

fn main() {
    if let Err(message) = run() {
        eprintln!("click-expand: {message}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if arguments.len() != 3 {
        return Err(
            "usage: click-expand <sidecar.click> <function> <ensure:N|effect:N|grouped>"
                .to_string(),
        );
    }
    let click_path = PathBuf::from(&arguments[0]);
    let click_source = fs::read_to_string(&click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let parent = click_path
        .parent()
        .unwrap_or_else(|| std::path::Path::new("."));
    let mut owned_sources = Vec::new();
    for source_path in
        verifying_source_paths(&click_source).map_err(|error| error.message().to_string())?
    {
        let disk_path = parent.join(&source_path);
        let source = fs::read_to_string(&disk_path)
            .map_err(|error| format!("failed to read `{}`: {error}", disk_path.display()))?;
        owned_sources.push((source_path, source));
    }
    let sources = owned_sources
        .iter()
        .map(|(path, source)| (path.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let claim = parse_claim(&arguments[2])?;
    let expanded = expand_c0_claim_source(&click_source, &sources, &arguments[1], claim)
        .map_err(|error| error.message().to_string())?;
    print!("{expanded}");
    Ok(())
}

fn parse_claim(source: &str) -> Result<CProofClaim, String> {
    if source == "grouped" {
        return Ok(CProofClaim::Grouped);
    }
    let (kind, index) = source
        .split_once(':')
        .ok_or_else(|| "claim must be `ensure:N`, `effect:N`, or `grouped`".to_string())?;
    let index = index
        .parse::<usize>()
        .map_err(|_| format!("invalid claim index `{index}`"))?;
    match kind {
        "ensure" => Ok(CProofClaim::Ensure(index)),
        "effect" => Ok(CProofClaim::Effect(index)),
        _ => Err(format!("unknown claim kind `{kind}`")),
    }
}
