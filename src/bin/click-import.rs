use std::env;
use std::path::{Path, PathBuf};

use click::languages::c::compiler_import::create_lock;

const USAGE: &str = "usage: click import lock <sidecar.click>\n\nCreates the checked compiler import artifact and sidecar.click.import.lock.json.";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click import: {message}");
        std::process::exit(1);
    }
}

fn entry() -> Result<(), String> {
    entry_with(env::args().skip(1))
}

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let arguments = arguments.into_iter().collect::<Vec<_>>();
    if matches!(arguments.as_slice(), [argument] if argument == "-h" || argument == "--help") {
        println!("{USAGE}");
        return Ok(());
    }
    let path = parse_arguments(arguments)?;
    create_lock(&path)
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<PathBuf, String> {
    let arguments = arguments.into_iter().collect::<Vec<_>>();
    let (command, sidecar, positional) = match arguments.as_slice() {
        [command, separator, sidecar] if separator == "--" => (command, sidecar, true),
        [command, sidecar] => (command, sidecar, false),
        _ => return Err(format!("expected `lock <sidecar.click>`\n{USAGE}")),
    };
    if command != "lock" {
        return Err(format!("unsupported import command `{command}`\n{USAGE}"));
    }
    if sidecar.is_empty() || (!positional && sidecar.starts_with('-')) {
        return Err("sidecar.click path must be a non-option path".into());
    }
    Ok(import_config_path(Path::new(sidecar)))
}

fn import_config_path(sidecar: &Path) -> PathBuf {
    let name = sidecar
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default();
    sidecar.with_file_name(format!("{name}.import.json"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derives_fixed_import_config_name() {
        assert_eq!(
            import_config_path(Path::new("demo/sidecar.click")),
            PathBuf::from("demo/sidecar.click.import.json")
        );
    }

    #[test]
    fn requires_lock_command_and_sidecar() {
        assert!(parse_arguments(Vec::<String>::new()).is_err());
        assert!(parse_arguments(["refresh".into(), "demo.click".into()]).is_err());
        assert_eq!(
            parse_arguments(["lock".into(), "demo.click".into()]).unwrap(),
            PathBuf::from("demo.click.import.json")
        );
    }
}
