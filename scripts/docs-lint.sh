#!/usr/bin/env bash
# Advisory prose lint. Deterministic structural and terminology rules live in
# tests/documentation.rs; Vale adds local editorial feedback when installed.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

if ! command -v vale >/dev/null 2>&1; then
    echo "vale not found; skipping advisory prose lint" >&2
    exit 0
fi

vale docs
