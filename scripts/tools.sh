#!/usr/bin/env bash
# Where the documentation tooling lives. Sourced by the mdBook wrappers and
# by `scripts/install-tools.sh`; not meant to be run.
#
# Tools are installed once per machine into a root shared by every checkout
# and worktree, keyed by version, so a fresh worktree never compiles them
# and the gate never touches the network. Override the root with
# `CLICK_TOOL_ROOT`, or point `MDBOOK_BIN` at an mdBook binary of your own.

mdbook_version="${MDBOOK_VERSION:-0.4.52}"
tool_root="${CLICK_TOOL_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/click/tools}"
mdbook_root="$tool_root/mdbook-$mdbook_version"
mdbook_bin="${MDBOOK_BIN:-$mdbook_root/bin/mdbook}"

# Fails with the setup instruction when mdBook is absent. The gate calls
# this; it never installs anything itself.
require_mdbook() {
    if [[ -x "$mdbook_bin" ]]; then
        return 0
    fi
    echo "error: mdBook $mdbook_version not found at $mdbook_bin" >&2
    echo "Install it once per machine (needs network) with:" >&2
    echo "    scripts/install-tools.sh" >&2
    exit 1
}
