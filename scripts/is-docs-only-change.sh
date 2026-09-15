#!/usr/bin/env bash
# Exit 0 when every newline-delimited changed path is documentation-only.
# Empty input is deliberately treated as a full check.
set -euo pipefail

found_path=false
while IFS= read -r path; do
    [[ -n "$path" ]] || continue
    found_path=true
    case "$path" in
        README.md|docs/*|issues/*|examples/*/README.md)
            ;;
        *)
            exit 1
            ;;
    esac
done

[[ "$found_path" == true ]]
