use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use click::lang::click::{verify_c0_sources_at, verifying_source_paths};

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
    let parent = click_path.parent().unwrap_or_else(|| Path::new("."));
    let sources = verifying_source_paths(&click_source)
        .map_err(|error| error.message().to_string())?
        .into_iter()
        .map(|name| {
            let source = fs::read_to_string(parent.join(&name))
                .map_err(|error| format!("failed to read `{name}`: {error}"))?;
            Ok((name, source))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let source_refs = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources_at(&click_source, &source_refs, line, column)
        .map_err(|error| error.message().to_string())?;
    Ok(())
}

fn parse_source_location(source: &str) -> Result<(PathBuf, usize, usize), String> {
    let (path_and_line, column) = source
        .rsplit_once(':')
        .ok_or_else(|| format!("invalid source location `{source}`; expected PATH:LINE:COLUMN"))?;
    let (path, line) = path_and_line
        .rsplit_once(':')
        .ok_or_else(|| format!("invalid source location `{source}`; expected PATH:LINE:COLUMN"))?;
    if path.is_empty() {
        return Err("source path must not be empty".to_string());
    }
    let line = line
        .parse::<usize>()
        .map_err(|_| format!("invalid source line `{line}`"))?;
    let column = column
        .parse::<usize>()
        .map_err(|_| format!("invalid source column `{column}`"))?;
    if line == 0 || column == 0 {
        return Err("source lines and columns are one-based".to_string());
    }
    Ok((PathBuf::from(path), line, column))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_location_from_the_right() {
        assert_eq!(
            parse_source_location("dir:with:colon/example.click:12:5"),
            Ok((PathBuf::from("dir:with:colon/example.click"), 12, 5))
        );
        assert!(parse_source_location("example.click:0:5").is_err());
        assert!(parse_source_location("example.click:12").is_err());
    }
}
