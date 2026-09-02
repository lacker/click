#!/usr/bin/env bash
# Installs the documentation tooling once per machine, into the shared root
# described in `scripts/tools.sh`. This is the only script that reaches the
# network; `scripts/check.sh` and the mdBook wrappers only look the tools up.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
# shellcheck source=scripts/tools.sh
source scripts/tools.sh

if [[ -x "$mdbook_bin" ]]; then
    echo "mdBook $mdbook_version already installed at $mdbook_bin"
    exit 0
fi

if ! command -v cargo >/dev/null 2>&1; then
    echo "error: cargo is required to install mdBook" >&2
    exit 1
fi

cargo install mdbook --locked --version "$mdbook_version" --root "$mdbook_root"
echo "installed mdBook $mdbook_version at $mdbook_bin"
