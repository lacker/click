#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
# shellcheck source=scripts/tools.sh
source scripts/tools.sh
require_mdbook

exec "$mdbook_bin" build "$@"
