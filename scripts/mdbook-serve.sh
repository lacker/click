#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

mdbook_version="${MDBOOK_VERSION:-0.4.52}"
tool_root="${MDBOOK_TOOL_ROOT:-target/tools}"
mdbook_bin="$tool_root/bin/mdbook"

if [[ ! -x "$mdbook_bin" ]]; then
    if ! command -v cargo >/dev/null 2>&1; then
        echo "error: cargo is required to install mdBook" >&2
        exit 1
    fi

    cargo install mdbook --locked --version "$mdbook_version" --root "$tool_root"
fi

exec "$mdbook_bin" serve "$@"
