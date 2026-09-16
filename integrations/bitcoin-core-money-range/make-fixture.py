#!/usr/bin/env python3
"""Regenerate the hermetic MoneyRange input closure from authenticated inputs.

This is a maintainer tool, not a verifier path. The test consumes the resulting
archive and command template without needing a network or a local Bitcoin tree.
"""

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile


COMMIT = "9be056a8a72b624dae9623b2f7bded92c2a21c91"
PACKAGES = {
    "libc6-dev": "0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae",
    "linux-libc-dev": "8bb258735b9dffbb111da778ebdd024750878e435ffd9dfcadcb6762ede6b4cf",
    "libstdc++-12-dev": "d28def6c23630432b57cb38a4c2fd67a79d4e0484027386ca6e8d6005c3d7a73",
    "libgcc-12-dev": "d720259380a84f2ffc6fe516eff5cbe9c8a005138e8d6a5748747ba4b3404a82",
    "libboost1.74-dev": "ba14fe04d7f138f874bd3ab3a20c4fd1e9f654e271449b8f3e48d20f942dbb93",
}
AMOUNT_SHA256 = "624a30c64528ce9873a1e440039cd261db81deecf14ed3003c171f7c2039ca50"
FEERATE_SHA256 = "a339052701a35a484a6d84e83d257ae643da2e2b635ccf105b44edf2f2ba30e8"
CLANG_SHA256 = "70c41308c6b84806a1e60b86b074ab4ad1e70ff692c4064ce79978bb101dd875"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked_bytes(path, expected):
    data = path.read_bytes()
    actual = digest(data)
    if actual != expected:
        raise ValueError(f"{path}: SHA-256 {actual}, expected {expected}")
    return data


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bitcoin-src", type=Path, required=True)
    parser.add_argument("--sysroot", type=Path, required=True)
    parser.add_argument("--packages", type=Path, required=True)
    parser.add_argument("--lock", type=Path, required=True)
    parser.add_argument("--compilation-database", type=Path, required=True)
    args = parser.parse_args()
    source = args.bitcoin_src.resolve(strict=True)
    sysroot = args.sysroot.resolve(strict=True)
    if git(source, "rev-parse", "HEAD").decode().strip() != COMMIT:
        raise ValueError("Bitcoin checkout is not the pinned v31.1 commit")
    if git(source, "status", "--porcelain", "--untracked-files=no"):
        raise ValueError("Bitcoin checkout has tracked local changes")
    for name, expected in PACKAGES.items():
        checked_bytes(args.packages / f"{name}.deb", expected)
    checked_bytes(Path("/opt/homebrew/opt/llvm@19/bin/clang++"), CLANG_SHA256)
    lock = json.loads(args.lock.read_text())
    if lock["source_sha256"] != FEERATE_SHA256 or lock["logical_source_sha256"] != AMOUNT_SHA256:
        raise ValueError("the import lock has different selected source digests")
    database_bytes = args.compilation_database.read_bytes()
    if lock["compilation_database_sha256"] != digest(database_bytes):
        raise ValueError("the CMake compilation database differs from the import lock")
    files = {}
    for path_string, entry in lock["preprocessor_files"].items():
        path = Path(path_string).resolve(strict=True)
        if path.is_relative_to(source):
            name = "bitcoin-src/" + str(path.relative_to(source))
            git_blob = git(source, "show", f"{COMMIT}:{path.relative_to(source)}")
            data = checked_bytes(path, entry["sha256"])
            if data != git_blob:
                raise ValueError(f"{path}: differs from the pinned Git tree")
        elif path.is_relative_to(sysroot):
            name = "sysroot/" + str(path.relative_to(sysroot))
            data = checked_bytes(path, entry["sha256"])
        elif "/clang/19/include/" in path_string:
            # The gate supplies the exact pinned Clang release and its resource headers.
            continue
        else:
            raise ValueError(f"unexpected preprocessor file: {path}")
        files[name] = data
    checked_bytes(source / "src/consensus/amount.h", AMOUNT_SHA256)
    checked_bytes(source / "src/policy/feerate.cpp", FEERATE_SHA256)
    files["bitcoin-src/COPYING"] = (source / "COPYING").read_bytes()
    for name in PACKAGES:
        notice = sysroot / "usr/share/doc" / name / "copyright"
        if notice.is_file():
            files[f"licenses/{name}.copyright"] = notice.read_bytes()

    # Prove that every packaged sysroot header came from one of the exact
    # pinned Debian archives, not merely from a similarly named local tree.
    remaining = {
        name: data for name, data in files.items() if name.startswith("sysroot/")
    }
    for name in PACKAGES:
        archive_data = subprocess.check_output(
            ["ar", "p", str(args.packages / f"{name}.deb"), "data.tar.xz"]
        )
        with tarfile.open(fileobj=io.BytesIO(archive_data), mode="r:xz") as package:
            for member in package:
                key = "sysroot/" + member.name.removeprefix("./")
                if key not in remaining or not member.isfile():
                    continue
                extracted = package.extractfile(member)
                if extracted is None or extracted.read() != remaining[key]:
                    raise ValueError(f"{key}: differs from {name}.deb")
                del remaining[key]
    if remaining:
        raise ValueError(f"sysroot files absent from pinned packages: {sorted(remaining)}")

    database = json.loads(database_bytes)
    matches = [row for row in database if row["file"].endswith("/src/policy/feerate.cpp")]
    if len(matches) != 1:
        raise ValueError("expected exactly one CMake feerate.cpp command")
    row = matches[0]
    if Path(row["file"]).resolve() != source / "src/policy/feerate.cpp":
        raise ValueError("selected CMake command is not for the pinned translation unit")
    if Path(row["directory"]).resolve() != source.parent / "bitcoin-build/src":
        raise ValueError("selected CMake command has an unexpected build directory")
    command = row["command"]
    if not command.startswith("/opt/homebrew/opt/llvm@19/bin/clang++ "):
        raise ValueError("selected CMake command has an unexpected compiler")
    for required in ("--target=x86_64-unknown-linux-gnu", "-std=c++20", "-c "):
        if required not in command:
            raise ValueError(f"selected CMake command lacks {required}")
    for forbidden in ("-fno-exceptions", "-fno-rtti", "-ffreestanding"):
        if forbidden in command:
            raise ValueError(f"selected CMake command has verifier-specific {forbidden}")
    # CMake uses /tmp for some paths on macOS and /private/tmp for others.
    root = str(source.parent)
    roots = {root, os.path.realpath(root), root.replace("/private/tmp/", "/tmp/")}
    for old_root in sorted(roots, key=len, reverse=True):
        command = command.replace(old_root + "/bitcoin-src", "@ROOT@/bitcoin-src")
        command = command.replace(old_root + "/bitcoin-build", "@ROOT@/bitcoin-build")
        command = command.replace(old_root + "/sysroot", "@ROOT@/sysroot")
    command = command.replace("/opt/homebrew/opt/llvm@19/bin/clang++", "@CLANGXX@")
    command = command.replace("/opt/homebrew/Cellar/llvm@19/19.1.7/lib/clang/19", "@RESOURCE_DIR@")
    if str(source.parent) in command or "/click-bitcoin-mac-cross-import/" in command:
        raise ValueError("unrelocated path in the selected CMake command")
    if "@ROOT@/bitcoin-src/src/policy/feerate.cpp" not in command:
        raise ValueError("selected CMake command lost the source translation unit")
    template = {
        "directory": "@ROOT@/bitcoin-build/src",
        "command": command,
        "file": "@ROOT@/bitcoin-src/src/policy/feerate.cpp",
        "output": row["output"],
    }

    here = Path(__file__).resolve().parent
    payload = io.BytesIO()
    with tarfile.open(fileobj=payload, mode="w") as archive:
        for name, data in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mode = 0o644
            info.mtime = 0
            archive.addfile(info, io.BytesIO(data))
    compressed = io.BytesIO()
    with gzip.GzipFile(fileobj=compressed, mode="wb", mtime=0) as stream:
        stream.write(payload.getvalue())
    archive_bytes = compressed.getvalue()
    (here / "input-closure.tar.gz").write_bytes(archive_bytes)
    (here / "feerate-command.json.in").write_text(json.dumps([template], indent=2) + "\n")
    manifest = {
        "bitcoin_commit": COMMIT,
        "amount_sha256": AMOUNT_SHA256,
        "feerate_sha256": FEERATE_SHA256,
        "packages_sha256": PACKAGES,
        "original_compilation_database_sha256": digest(database_bytes),
        "source_lock_identity": lock["identity"],
        "origin_clang_sha256": CLANG_SHA256,
        "input_file_count": len(files),
        "input_closure_sha256": digest(archive_bytes),
    }
    (here / "fixture-provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
