# Bitcoin Core `MoneyRange` on a macOS host

This opt-in integration example imports the unchanged inline `MoneyRange` from
Bitcoin Core v31.1 through a real `src/policy/feerate.cpp` CMake compilation
command. The host can be Apple Silicon macOS: Clang targets x86-64 Linux using
Linux headers in `inputs/sysroot`. The setup generates a compilation database;
it does not claim to link or run Bitcoin Core binaries.

The upstream tag is pinned to commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`. The expected SHA-256 values
are `624a30c64528ce9873a1e440039cd261db81deecf14ed3003c171f7c2039ca50`
for `src/consensus/amount.h` and
`a339052701a35a484a6d84e83d257ae643da2e2b635ccf105b44edf2f2ba30e8`
for `src/policy/feerate.cpp`. Check the commit and both hashes before importing;
do not copy the function into this example.

The tested toolchain was Homebrew Clang **19.1.7**, CMake **3.31.6**, and these
Debian Bookworm x86-64 development packages extracted into `inputs/sysroot`:

| Package | Version | SHA-256 of `.deb` |
| --- | --- | --- |
| `libc6-dev` | `2.36-9+deb12u14` | `0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae` |
| `linux-libc-dev` | `6.1.176-1` | `8bb258735b9dffbb111da778ebdd024750878e435ffd9dfcadcb6762ede6b4cf` |
| `libstdc++-12-dev` | `12.2.0-14+deb12u1` | `d28def6c23630432b57cb38a4c2fd67a79d4e0484027386ca6e8d6005c3d7a73` |
| `libgcc-12-dev` | `12.2.0-14+deb12u1` | `d720259380a84f2ffc6fe516eff5cbe9c8a005138e8d6a5748747ba4b3404a82` |
| `libboost1.74-dev` | `1.74.0+ds1-21` | `ba14fe04d7f138f874bd3ab3a20c4fd1e9f654e271449b8f3e48d20f942dbb93` |

Put the unmodified checkout at `inputs/bitcoin-src`, the extracted development
packages at `inputs/sysroot`, and use `inputs/bitcoin-build` for the CMake
build directory. From the repository root, generate the compilation database:

```sh
cmake -S integrations/bitcoin-core-money-range/inputs/bitcoin-src \
  -B integrations/bitcoin-core-money-range/inputs/bitcoin-build \
  -DCMAKE_TOOLCHAIN_FILE="$PWD/integrations/bitcoin-core-money-range/linux-x86_64-clang19.cmake" \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DBoost_DIR="$PWD/integrations/bitcoin-core-money-range/inputs/sysroot/usr/lib/x86_64-linux-gnu/cmake/Boost-1.74.0" \
  -Dboost_headers_DIR="$PWD/integrations/bitcoin-core-money-range/inputs/sysroot/usr/lib/x86_64-linux-gnu/cmake/boost_headers-1.74.0" \
  -DBUILD_BITCOIN_BIN=OFF -DBUILD_DAEMON=OFF -DBUILD_CLI=OFF \
  -DBUILD_TX=OFF -DBUILD_UTIL=OFF -DBUILD_TESTS=OFF -DBUILD_BENCH=OFF \
  -DBUILD_GUI=OFF -DBUILD_KERNEL_LIB=OFF -DBUILD_UTIL_CHAINSTATE=OFF \
  -DENABLE_WALLET=OFF -DENABLE_IPC=OFF -DWITH_ZMQ=OFF
```

The generated `compile_commands.json` must contain one
`src/policy/feerate.cpp` command with `--target=x86_64-unknown-linux-gnu`,
`-std=c++20`, and no verifier-specific exception or RTTI overrides. The
toolchain file supplies the Linux sysroot, standard-library include paths, and
Clang resource directory needed by both the compiler driver and LibTooling.
Some CMake link probes warn because this header-only setup does not install a
Linux runtime; successful configuration and the selected compile command, not
a binary build, are the setup requirements.

Then build the pinned exporter and explicitly refresh the local lock:

```sh
scripts/build-cpp-exporter.sh
cargo run --bin click -- import lock integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- verify integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- profile integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- audit integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- expand --claim MoneyRange.contract integrations/bitcoin-core-money-range/MoneyRange.click
```

`MoneyRange.click.import.json` and the sidecar are versioned; this full-checkout
workflow's checkout, sysroot, compilation database, semantic artifact, and lock
remain local. The lock binds the selected command, exact source and header
bytes, all textual headers Clang opened (including sysroot and Clang resource
headers), the resolved target of each path, exporter, and observed semantic
profile. Once locked, verification loads the artifact offline without invoking
Clang. A different checkout location or toolchain command requires an explicit
refresh.

## Hermetic gate fixture

The normal `scripts/check.sh` gate also re-exports and verifies this same
`MoneyRange` sidecar without a network or a local Bitcoin checkout. Its
[`input-closure.tar.gz`](input-closure.tar.gz) contains only the 15 Bitcoin
files and 292 Linux sysroot headers observed by the pinned import, plus source
and package notices. The Bitcoin bytes were checked against the exact v31.1
Git tree; every sysroot header was matched to a member of one of the five
SHA-256-pinned Debian packages above. The gate checks the archive digest,
the unchanged selected header and translation unit, the 320-file Clang input
inventory, and re-runs semantic export and proof verification with Clang
19.1.7. No hand-copied function or precomputed semantic artifact is used.

[`feerate-command.json.in`](feerate-command.json.in) is the selected command
from the real Bitcoin CMake-generated compilation database, with only the
checkout/build/sysroot paths and pinned Clang executable/resource paths
relocated for the test machine. [`fixture-provenance.json`](fixture-provenance.json)
records the release commit, original database and import-lock identities,
archive digest, and source, package, and originating Clang executable hashes.
The gate does not rerun Bitcoin's whole CMake configuration; that remains the
opt-in full-checkout workflow above. It also does not build or run Bitcoin.

To regenerate the hermetic fixture after creating the local lock above, put
the five downloaded `.deb` archives in `inputs/packages` under the short names
shown in the table (for example `libc6-dev.deb`), then run:

```sh
python3 integrations/bitcoin-core-money-range/make-fixture.py \
  --bitcoin-src integrations/bitcoin-core-money-range/inputs/bitcoin-src \
  --sysroot integrations/bitcoin-core-money-range/inputs/sysroot \
  --packages integrations/bitcoin-core-money-range/inputs/packages \
  --lock integrations/bitcoin-core-money-range/MoneyRange.click.import.json.lock \
  --compilation-database integrations/bitcoin-core-money-range/inputs/bitcoin-build/compile_commands.json
```

Regeneration checks the Git tree, local source bytes, Debian archives and
extracted header bytes, originating Clang executable, and selected compile
flags before changing the checked-in closure. A changed archive also requires
deliberately updating the pinned digest in the gate test after review.

The sidecar also contains four one-call, modular `executes MoneyRange`
proofs. They apply the verified upstream function contract to an arbitrary
`const CAmount&` whose value is respectively `-1`, `0`, `MAX_MONEY`, or
`MAX_MONEY + 1`, and establish false, true, true, or false while returning
the reference's owned cell unchanged. These are proof-level callers: they
introduce no C++ wrapper, alternate implementation, or verifier-specific
build flag.

The gate also rejects an exclusive upper-bound claim against the unchanged
upstream function. It refuses to load the locked artifact after changes to
`amount.h`, a transitive Linux header, the CMake compile command, or the
configured profile. Selecting `MoneyRange` from a different upstream header
fails refresh, and that rejected selector cannot load the old artifact.

The gate profiles the complete upstream proof, resolves every profiled tactic
to its sidecar location, and audits all 14 smart-tactic sites. Each site is
expanded against the same locked import, the resulting certificate is checked
by ordinary verification and a retained audit session, and the expanded
claim has fewer smart sites. This covers the range contract and all four
boundary theorems without invoking Clang during verification or expansion.

This is one function under one Clang profile, not general Bitcoin Core or
Linux binary verification.
