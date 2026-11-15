# Checked C/Rust Adler-32 correspondence

The unchanged pinned zlib C implementation and adler2 Rust implementation
satisfy [one mathematical specification](adler32-spec.click).
[correspondence.click](adler2/correspondence.click) derives native return-word
equality from their checked postconditions, matching initial state, length,
and entry bytes. This is a composition of separately checked programs;
it does not import a mixed C/Rust executable or prove an FFI boundary.

## Matched calls

Let `n` be any `uint64` length both buffers admit, and let `A0` and `B0` each
be from 0 through 65520. Give C a seed whose decoded low/high 16-bit fields
are `A0`/`B0`, and Rust a receiver with those fields. The C buffer must be
nonnull. Each caller supplies the read authority required by its contract.
The buffers may be distinct allocations, provided their entry states have
the same byte at every index `k < n`.

| Checked producer | Result observation |
| --- | --- |
| C [canonical.click](zlib/canonical.click) | `to_integer(c_result) == adler_spec_checksum_u64(c_bytes, n, A0, B0)` |
| Rust [public-general.click](adler2/public-general.click), then [checksum.click](adler2/checksum.click) | `to_integer(rust_result) == adler_spec_checksum_u64(rust_bytes, n, A0, B0)` |

`adler_c_rust_results` uses the checked [full-width specification](adler32-spec-u64.click)'s extensionality theorem
to identify these two mathematical checksums. `adler_result_widen` proves that
converting the Rust `uint32` word to the C LP64 `uint64` word preserves its
Integer observation. Checked uint64 injectivity then gives
`c_result == rust_result as uint64`. The result premises come from the producers;
the correspondence theorem does not establish memory authority or execute them.

For the standard seed, take `A0=1`, `B0=0` and use Rust's checked
`adler32_slice`. For saved-state updates, the checked
[from_checksum](adler2/restoration.click) decodes all `uint32` words, but the
update proof requires both decoded fields to be canonical. The C seed may have
bits above bit 31: its original masking ignores them. Match the decoded fields,
not the full LP64 seed word.

## Incremental calls and reset

The actual [C two-call client](zlib/incremental.click) and
[Rust two-write client](adler2/incremental.click) independently produce the
whole-input checksum. Instantiate the same correspondence theorem with their
return words and whole-input entry states. Both splits may range from zero
through the total length; their split positions need not be equal. The C
client requires both call pointers to be nonnull, including empty pieces.
Rust's [saved/restored client](adler2/resumed.click) has the same standard-seed
whole-input result observation.

C's [null reset](zlib/reset.click) returns `1` for any seed and any native
length other than `1`, with no buffer view. The unchanged one-byte fast path
precedes the null check, so `NULL,1` is excluded. Rust's checked
[new/default constructors](adler2/public-constructors.click) produce fields
`A=1,B=0`; the checked getter packs those as `1`.
`adler_c_rust_reset` connects these exact postconditions. An ordinary empty
nonnull update preserves the supplied state and is not a reset request.

## Reproduce

Install Click, then run these preparation commands from the repository root:

```sh
click add rust
python3 scripts/prepare-adler32-demo.py /tmp/click-adler32-demo
```

Replace `VERSION` with the matching Click release. The destination must not
exist. The script copies the original sources, licenses, prepared artifacts and
locks. It assembles the canonical Rust proof fragments into complete sidecars
and includes the C producers' helper bodies in their own sidecars. It runs no
compiler or verifier and changes no computation or proof claim. Python is needed
only for this preparation step.

The resulting directory is self-contained and may be moved outside the checkout.
With the installed `click`, verify every producer body and the result/reset
correspondence using ordinary bounds:

```sh
cd /tmp/click-adler32-demo
click verify design/adler32/project/zlib/canonical-demo.click
click verify design/adler32/project/zlib/incremental-demo.click
click verify design/adler32/project/zlib/reset-demo.click
click verify design/adler32/project/adler2/public-demo.click
click verify design/adler32/project/adler2/incremental-demo.click
click verify design/adler32/project/adler2/resumed-demo.click
click verify design/adler32/project/adler2/correspondence.click
```

Verification uses the committed locks offline; it needs neither GCC, Charon,
rustc, Python nor the original checkout. Do not run `click import lock` over the C
fixtures without their recorded compiler setup. Rust refresh is a separate
operation through the installed bundle. Importing a theorem or function contract
does not verify its body: the assembled producer sidecars include those bodies,
and the correspondence theorem is checked separately. This remains composition
through a shared specification, with the matched-input and length conditions
above, rather than verification of an FFI boundary.

The nightly test `adler32_prepared_demonstration_verifies_offline` executes
these commands after relocating the prepared demonstration, with an empty
`PATH` and no frontend or user Rust toolchain. A differential regression checks
that the assembled Rust sidecars retain the canonical proof tokens.

For contributor-only live extraction, install pinned Charon and set
`CLICK_CHARON` using `scripts/build-charon.sh --install-toolchain`. From the
repository root, the existing targeted regressions remain available below.

The bounded normal regression checks correspondence bodies and rejects
missing byte matching, mismatched initial state, an incorrect result, and a
wrong constructor field:

```sh
cargo test --test compiler_import adler_c_rust_correspondence_requires_matched_inputs
cargo test --test compiler_import pinned_zlib_null_reset_is_independent_of_seed_and_nonunit_length
```

These individually selected nightly fixtures check producer bodies and
complete expansions. They are reproducible commands, not a request to run
the entire nightly suite:

```sh
cargo test --test compiler_import adler_c_rust_correspondence_expands_with_checked_dependencies -- --ignored
cargo test --test compiler_import pinned_zlib_canonical_seed_matches_checked_shared_specification_offline -- --ignored
cargo test --test rust_import charon_adler2_general_public_checksum_tools_check_all_original_bodies -- --ignored
cargo test --test compiler_import pinned_zlib_incremental_c_matches_checked_shared_specification_offline -- --ignored
cargo test --test rust_import charon_adler2_incremental_client_tools_check_all_original_bodies -- --ignored
cargo test --test rust_import charon_adler2_resumed_client_tools_check_all_original_bodies -- --ignored
```

The proof covers the original scalar, vector/block, NMAX batch and tail paths
under these contracts, together with termination and byte preservation.
Noncanonical update state,
allocation lifetime and an FFI calling convention are outside this claim.
Compiler import and library trust boundaries remain those documented by the
[Rust trial](../../charon-trial/README.md) and [C fixture](zlib/README.md).
