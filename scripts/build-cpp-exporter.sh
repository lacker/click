#!/usr/bin/env bash
# Build the repository-owned semantic exporter against the pinned Clang API.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

expected_version=19.1.7
if [[ -n "${LLVM_CONFIG:-}" ]]; then
    llvm_config="$LLVM_CONFIG"
elif command -v llvm-config-19 >/dev/null 2>&1; then
    llvm_config="$(command -v llvm-config-19)"
elif [[ -x /opt/homebrew/opt/llvm@19/bin/llvm-config ]]; then
    llvm_config=/opt/homebrew/opt/llvm@19/bin/llvm-config
elif [[ -x /usr/lib/llvm-19/bin/llvm-config ]]; then
    llvm_config=/usr/lib/llvm-19/bin/llvm-config
else
    echo "error: LLVM $expected_version development tools are required" >&2
    echo "Set LLVM_CONFIG to the pinned llvm-config executable." >&2
    exit 1
fi

actual_version="$("$llvm_config" --version)"
if [[ "$actual_version" != "$expected_version" ]]; then
    echo "error: LLVM $expected_version is required; $llvm_config reports $actual_version" >&2
    exit 1
fi

llvm_bindir="$("$llvm_config" --bindir)"
llvm_libdir="$("$llvm_config" --libdir)"
clangxx="${CLANGXX:-$llvm_bindir/clang++}"
if [[ ! -x "$clangxx" ]]; then
    echo "error: pinned clang++ not found at $clangxx" >&2
    exit 1
fi
if ! "$clangxx" --version | head -n 1 | grep -Fq "$expected_version"; then
    echo "error: $clangxx is not Clang $expected_version" >&2
    exit 1
fi

clang_cpp=
for candidate in \
    "$llvm_libdir/libclang-cpp.dylib" \
    "$llvm_libdir/libclang-cpp.so.19.1" \
    "$llvm_libdir/libclang-cpp.so.19" \
    "$llvm_libdir/libclang-cpp.so"; do
    if [[ -f "$candidate" ]]; then
        clang_cpp="$candidate"
        break
    fi
done
if [[ -z "$clang_cpp" ]]; then
    echo "error: the Clang $expected_version C++ API library was not found in $llvm_libdir" >&2
    exit 1
fi

read -r -a llvm_cxxflags <<<"$("$llvm_config" --cxxflags)"
read -r -a llvm_ldflags <<<"$("$llvm_config" --ldflags)"
read -r -a llvm_system_libs <<<"$("$llvm_config" --system-libs)"
read -r -a llvm_libs <<<"$("$llvm_config" --libs)"

build_directory="${CLICK_CPP_EXPORTER_BUILD_DIR:-target/cpp-exporter}"
output="$build_directory/click-cpp-exporter"
temporary="$output.tmp.$$"
mkdir -p "$build_directory"
trap 'rm -f "$temporary"' EXIT

"$clangxx" \
    "${llvm_cxxflags[@]}" \
    -std=c++20 \
    -Wall \
    -Wextra \
    -Werror \
    -Wno-unused-parameter \
    tools/cpp-exporter/main.cpp \
    "${llvm_ldflags[@]}" \
    "-Wl,-rpath,$llvm_libdir" \
    "$clang_cpp" \
    "${llvm_libs[@]}" \
    "${llvm_system_libs[@]}" \
    -o "$temporary"
mv "$temporary" "$output"
trap - EXIT

absolute_build_directory="$(cd "$build_directory" && pwd -P)"
printf '%s\n' "$absolute_build_directory/click-cpp-exporter"
