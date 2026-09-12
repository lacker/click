# Borrow semantics investigation probes

Synthetic, standalone probes for the
[resource/borrowing investigation](../borrow-semantics-investigation.md).
These are synthetic examples, not a supported Rust/C++ verification path.
The original language probes explore later frontend support; the two C
contract-migration probes also support the P1 `fix-views` investigation. The
Rust rejection probes are intentionally invalid programs; successful
reproduction requires their compilation to fail.

## Observed results

| Probe | Observed result |
| --- | --- |
| `alias.c` + `alias.click` | Click verifies the aliased read returns the newly stored 7. |
| `alias.c` + `alias-owned.click` | The same C and result verify with ownership alone, without an overlapping view. |
| `field-split.c` + `field-split.click` | A setter owns the changed field and views the other field; its caller preserves the viewed field and recovers the folded resource. |
| `borrows.rs` | Rust compilation and all runtime assertions pass. |
| `shared_write_rejected.rs` | Rust rejects assignment with E0506. |
| `parent_write_rejected.rs` | Rust rejects assignment with E0506. |
| `returned_write_rejected.rs` | Rust rejects assignment with E0506. |
| `alias_and_cleanup.cpp` | C++ compilation and all runtime assertions pass; CFG has an implicit destructor on both return paths. |

Recorded with Rust 1.98.1 (`48a229cea`, 2026-09-01), installed nightly
`nightly-2026-06-16` for unoptimized MIR, and Apple Clang 16.0.0
(`clang-1600.0.26.6`) on ARM64 macOS. The Click probe uses the built verifier
from `bf0399b5` and its named `x86_64-linux-kernel` profile. Its executable was
built in the preceding roadmap worktree, whose verifier source is identical
to the investigation base. No compiler or verifier timeout was encountered.

The existing `mdtests/pointer_params_may_alias_without_separate.md` regression
also passed under its normal bounded fixture runner on that base: the
incorrect unchanged-value postcondition is rejected. That is complementary
negative evidence to the positive C alias probe.

The two contract-migration probes were added for the P1
[fix-views investigation](../../issues/fix-views.md) at base `79411f40` and
also passed ordinary bounded verification. `field-split.c` is copied unchanged
from `mdtests/composite_piece_caller_frames_viewed_field.md`; its sidecar views
only the unchanged field. These probes validate migration options under the
current verifier, not the proposed stronger borrowing rules. They used the
same target profile and unchanged verifier implementation described above.

## Reproduce from the repository root

Verify the C claim through the ordinary Click engine:

```console
cargo run --bin click -- verify design/borrow-probes/alias.click
cargo run --bin click -- verify design/borrow-probes/alias-owned.click
cargo run --bin click -- verify design/borrow-probes/field-split.click
```

Compile and execute the valid Rust examples:

```console
rustc --edition=2024 design/borrow-probes/borrows.rs -o /tmp/click-borrow-probe-rust
/tmp/click-borrow-probe-rust
```

Run each negative compilation separately. Each must exit nonzero with E0506:

```console
rustc --edition=2024 --crate-type=lib design/borrow-probes/shared_write_rejected.rs -o /tmp/click-shared-write-rejected.rlib
rustc --edition=2024 --crate-type=lib design/borrow-probes/parent_write_rejected.rs -o /tmp/click-parent-write-rejected.rlib
rustc --edition=2024 --crate-type=lib design/borrow-probes/returned_write_rejected.rs -o /tmp/click-returned-write-rejected.rlib
```

Inspect MIR; the pinned nightly command requires that toolchain to be installed:

```console
rustc --edition=2024 --emit=mir design/borrow-probes/borrows.rs -o /tmp/click-borrow-probe.mir
rustc +nightly-2026-06-16 --edition=2024 -Zmir-opt-level=0 --emit=mir design/borrow-probes/borrows.rs -o /tmp/click-borrow-probe-unoptimized.mir
```

Compile and execute the valid C++ examples, then inspect the CFG:

```console
clang++ -std=c++20 design/borrow-probes/alias_and_cleanup.cpp -o /tmp/click-borrow-probe-cpp
/tmp/click-borrow-probe-cpp
clang++ -std=c++20 -Xclang -analyze -Xclang -analyzer-checker=debug.DumpCFG -fsyntax-only design/borrow-probes/alias_and_cleanup.cpp
```

MIR and CFG output are human inspection artifacts and are not checked into the
repository or parsed as a production API. The ordinary repository gate does
not execute these Rust/C++ probes; rerun the commands when revisiting the
investigation. Compiler rejection tests cover safe-source borrowing only;
Miri and an unsafe-reference model were not exercised.
