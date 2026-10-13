#!/usr/bin/env bash
# Write the AI reference's generated site files into the rendered book, next
# to index.html: llms.txt, the single-file bundle click-reference.md, and each
# page's Markdown source. Run it after scripts/mdbook-build.sh;
# scripts/check.sh --docs-only does both. The generator is
# tests/support/ai_reference.rs. Usage: scripts/build-ai-reference.sh [DIR]
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

output="${1:-$PWD/target/click-docs}"
CLICK_AI_REFERENCE_OUT="$output" exec cargo test --quiet --test documentation \
    ai_reference_site_files_generate
