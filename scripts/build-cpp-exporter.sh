#!/usr/bin/env bash
# Build the repository-owned semantic exporter against the pinned Clang API.
#
# `--check` only checks that the pinned toolchain is installed, without
# building: it exits 0 when it is, and otherwise names what is missing.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

check_only=""
if [[ "${1:-}" == "--check" ]]; then
    check_only=1
elif [[ -n "${1:-}" ]]; then
    echo "usage: scripts/build-cpp-exporter.sh [--check]" >&2
    exit 2
fi

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

if [[ ! -x "$llvm_config" ]]; then
    echo "error: LLVM_CONFIG names $llvm_config, which is not an executable" >&2
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

# Clang ships no C++ standard library on Linux: it borrows the headers of the
# newest GCC installation it finds. A distribution update that moves the
# libstdc++ runtime forward creates a newer GCC directory without its headers
# unless the matching libstdc++-N-dev package is installed, and the exporter
# build then fails deep inside a compile on `<algorithm>`. Check for that here
# and name the missing package.
if ! printf '#include <algorithm>\nint main() { return 0; }\n' \
    | "$clangxx" -std=c++20 -x c++ -fsyntax-only - >/dev/null 2>&1; then
    selected_gcc="$("$clangxx" -v -x c++ -E /dev/null 2>&1 \
        | sed -n 's/^Selected GCC installation: //p')"
    echo "error: $clangxx cannot compile a C++ program that includes <algorithm>" >&2
    if [[ -n "$selected_gcc" ]]; then
        gcc_version="${selected_gcc##*/}"
        echo "It selected the GCC installation at $selected_gcc, which has no C++ standard library headers." >&2
        echo "Install the matching headers (on Debian/Ubuntu: libstdc++-${gcc_version}-dev)," >&2
        echo "or point it at an installation that has them, for example:" >&2
        echo "  CCC_OVERRIDE_OPTIONS='+--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/<version>'" >&2
    else
        echo "Install the C++ standard library development headers for the pinned toolchain." >&2
    fi
    exit 1
fi

if [[ -n "$check_only" ]]; then
    exit 0
fi

read -r -a llvm_cxxflags <<<"$("$llvm_config" --cxxflags)"
read -r -a llvm_ldflags <<<"$("$llvm_config" --ldflags)"
read -r -a llvm_system_libs <<<"$("$llvm_config" --system-libs)"
read -r -a llvm_libs <<<"$("$llvm_config" --libs)"

build_directory="${CLICK_CPP_EXPORTER_BUILD_DIR:-target/cpp-exporter}"
output="$build_directory/click-cpp-exporter"
temporary="$output.tmp.$$"
mkdir -p "$build_directory"

# The build takes about 35 seconds and every gate run asks for it, so reuse
# the last binary when nothing that goes into it has changed: the exporter
# source, this script, and the toolchain and flags it resolved to.
stamp="$output.stamp"
fingerprint="$(
    {
        cat tools/cpp-exporter/* "${BASH_SOURCE[0]}"
        "$clangxx" --version
        printf '%s\n' "$clangxx" "$clang_cpp" "${CCC_OVERRIDE_OPTIONS:-}" \
            "${llvm_cxxflags[@]}" "${llvm_ldflags[@]}" "${llvm_libs[@]}" "${llvm_system_libs[@]}"
    } | cksum
)"
if [[ -x "$output" && -f "$stamp" && "$(cat "$stamp")" == "$fingerprint" ]]; then
    absolute_build_directory="$(cd "$build_directory" && pwd -P)"
    printf '%s\n' "$absolute_build_directory/click-cpp-exporter"
    exit 0
fi
rm -f "$stamp"
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
printf '%s\n' "$fingerprint" > "$stamp"

absolute_build_directory="$(cd "$build_directory" && pwd -P)"
printf '%s\n' "$absolute_build_directory/click-cpp-exporter"
