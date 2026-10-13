# Experimental Rust imports

Click accepts a small safe, monomorphic subset of Rust 2021 and 2024. Its Rust importer
uses pinned, unmodified [Charon](https://github.com/AeneasVerif/charon) after rustc
type and borrow checking. Every imported body follows the native ULLBC control
flow path into Click's shared execution, memory, and certificate rules.
Verification uses the same sidecars, tactics, and bounded engine as C and C++.
[Language coverage](coverage.md) compares the Rust subset with C and C++.

Charon is the extraction backend; `scripts/build-charon.sh` builds the pinned
version. Rust support is experimental: it needs a repository checkout and a
separately built importer, and covers the subset listed in
[Language coverage](coverage.md).

The working example is
[`examples/basic-rust/borrow.rs`](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.rs),
with its
[sidecar](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.click).
It covers a scalar branch, a mutable reference helper that writes through a
local reborrow and then reuses its parent, and a caller proving a struct field's
final value while preserving its other field. A shared field borrow remains
stable while the disjoint field is mutated.

## Reproduce the example

Run `scripts/setup-environment.sh` once for Click's pinned stable toolchain.
Build pinned Charon and install its separate compiler with
`scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
cargo run --bin click -- profile examples/basic-rust/borrow.click
cargo run --bin click -- audit examples/basic-rust/borrow.click
cargo run --bin click -- expand --claim update.contract --in-place examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

Locked Rust imports also support focused proof tracing:

```sh
cargo run --bin click -- verify --trace-proof update examples/basic-rust/borrow.click
```

Use a function or theorem name declared in the sidecar. `--trace-to LINE[:COLUMN]`
selects a written tactic within that proof. Only the named proof is checked;
other function contracts remain interfaces. Tracing validates the ordinary
import lock and does not rerun the compiler.

The import configuration selects one `.rs` file, the exporter executable,
and an artifact output. Refresh runs the compiler with a bounded process and
writes the artifact and input lock. Ordinary verification loads those files
without executing the compiler. Source, configuration, artifact, or profile
changes require refresh. The saved lock includes the compiler/exporter identity. After updating the
extractor or adapter semantics, refresh existing imports. Configurations use
schema 3 and native `.ullbc` artifacts. Omitting `backend` selects Charon;
`"charon"` and the historical `"charon-trial"` spelling are also accepted.
Schema 2 is rejected with a migration diagnostic. The normal example gate
checks locked native inputs offline, while the nightly gate's live Charon
tests refresh and verify all 16 original Rust fixtures.

## Locked crates and qualified declarations

Schema 3 retains the existing one-file Rust 2024 interface. Schema 4 adds an
explicit crate root and compiler configuration:

```json
{
  "schema": 4,
  "language": "rust",
  "target": "x86_64-unknown-linux-gnu",
  "source": "src/lib.rs",
  "exporter": "../../../target/charon/debug/charon",
  "artifact": "crate.ullbc",
  "crate": {
    "name": "adler2",
    "edition": "2021",
    "features": ["std"],
    "roots": ["adler2::adler32_slice"],
    "files": ["src/lib.rs", "src/algo.rs"]
  }
}
```

This invokes rustc directly; it does not execute Cargo manifests or build
scripts, resolve third-party dependencies, or enable features implicitly.
Editions 2021 and 2024 are supported. Roots are explicit qualified paths.
All compiler-read inputs, including unused modules and included data, must
appear exactly once in `files`. rustc dep-info checks that closure. Files must
be regular, use normalized relative paths, and stay inside the configuration
directory without symlinks. Environment-dependent source macros are rejected.

Extraction compiles a private snapshot of those bytes. The aggregate source
hash covers every input, and configuration hashes bind the root, edition,
features, and entry points. Ordinary loading rechecks the full closure
without executing a compiler. Schema-4 artifacts use the versioned
`click-charon-crate-v4` envelope; existing schema-3 locks keep their identity.

Module definitions and inherent methods retain compiler-resolved identities.
Proof identifiers encode tagged, length-prefixed path components, so `a::read`,
`b::read`, and `a_read` remain distinct even when their leaf names overlap.
Inherent methods include their resolved receiver type. Calls still follow
Charon's declaration IDs and execute imported bodies; names never grant a
library summary. Concrete assignment operators retain their trait,
implementation, signature, and associated-item checks across module paths.

Schema 4 supports by-value returns of supported flat records, including owned
array fields and records with `Drop`. The concrete return layout enters the
kernel's aggregate-return interface: field values copy into fresh caller
storage, and Rust live flags transfer ownership once. Reference, array, and
nested-record returns remain unsupported. By-value flat-record parameters use
the kernel aggregate-parameter interface: each callee receives independent
storage. Compiler moves consume the caller’s live value; compiler copies
preserve it. Record copies require plain scalar or supported array fields
and no destructor. These ownership events are checked at calls as well as
local assignments. Array parameters by value remain unsupported.

Contracts take owned parameters as `input: RecordType`. Use
`old(input.field)` for entry values when the body modifies the parameter.
Its private bytes have internal ownership and cannot be declared as contract
input resources. Passing a pointer field still requires the pointee's own
resource clauses; copying a record grants no ownership over its pointees.

Schema 4 imports local named scalar constants (`bool`, `i32`, `u8`, `u16`,
`u32`, and target-width `usize`) with straight-line arithmetic initializers.
Each initializer retains its qualified identity and executes its imported CFG;
constant reads call that body through the ordinary checked function interface.
Sidecars prove an initializer contract before using its value in callers.
For example, a `CHUNK_SIZE` initializer computing `5552 * 4` needs a verified
`uint64 <qualified-initializer>() { ensures result == 22208u64; }` contract.
Overflow and other arithmetic obligations remain checked. Statics, anonymous
or trait constants, generic constants, references, initializer branches,
dependencies on other constants, and `const fn` calls remain unsupported.

Concrete `core::default::Default` implementations on local records execute
their imported bodies. Dispatch checks the standard diagnostic identity,
qualified trait path, associated method, implementation ID, signatures, and
return type. Ordinary constructors use the same body and return path. Sidecar
contracts use `struct <qualified-record> <function>(...)` and can state
`ensures result.field == value;`; those contracts must verify before callers
can use them.

The unchanged adler2 trial proves `Adler32::default` and `Adler32::new` return
`a = 1`, `b = 0`. Concrete assignment operators also accept supported
by-value record operands through the checked call interface. Selecting the
complete checksum loop now produces a locked, prepared import, and its
`MOD` and `CHUNK_SIZE` initializer contracts verify. Its unchanged whole body
proves bounds, termination, and both final checksum fields against the common
specification for canonical seeds and lengths through 2,147,483,647 bytes,
including full batches and both remainders. General trait dispatch and arbitrary Rust
crates remain outside the supported subset.

## Signatures in Rust syntax

A sidecar for a Rust source states a function's signature as Rust does,
with Rust type names, and cast with `as`:

<!-- verified-example: tests/fixtures/rust-verification/fn_signatures.click -->
```click
verifying "borrow.rs";

fn add_byte(sum: u32, byte: u8) -> u32 {
    requires sum <= 4294967040u32;
    ensures result == sum + byte as u32;
} by { execute(); simp(); }

fn times_three(value: u32) -> u32 {
    requires value <= 1431655765u32;
    ensures result == value * 3u32;
} by { execute(); simp(); }

fn reduce(value: u32) -> u32 {
    ensures result == value % 65521u32;
} by { execute(); simp(); }
```

A Rust source's function contracts require this form. A C-shaped signature
is refused with a suggestion of the `fn` spelling. A field through a
reference is `p.f`; `p->f` is refused. The
sidecar parser accepts every Rust integer and float type name, `bool`, `()`,
and a struct by name, but the importer admits only the types in
[Supported semantics](#supported-semantics); `usize` and `isize` are 64 bits. `expr as T` takes a
scalar type and binds as in Rust, tighter than a binary operator.

A parameter may be a reference, `&T` or `&mut T`, to a scalar or a struct.
The contract names what it refers to as Rust does: `*value` for the
referent and `parent.left` for a field. The type does not grant authority;
the contract still states `views` or `owns`. Lifetimes may be written or
left out, `fn pick<'a>(value: &'a u32) -> u32`; the contract does not use
them, and a type parameter is refused, as the importer refuses a generic
function. A tuple struct's field is named by its position, `self.0`.

A diagnostic about a function whose signature is written this way, and the
proof `click expand` writes for it, spell its places the same way: a
slice's length `bytes.len()`, a cast `(x as u32)`, and a field through a
reference `p.field`.

<!-- verified-example: tests/fixtures/rust-verification/references.click -->
```click
verifying "borrow.rs";

fn choose(x: i32) -> i32 {
    requires 0 <= x;
    ensures result == (if x < 7 { x + 1 } else { 7 });
} by {
    execute();
    simp();
}

fn set_seven(value: &mut i32) {
    owns *value;
    ensures *value == 8;
} by {
    execute();
    simp();
}

fn update(parent: &mut Pair) -> i32 {
    owns parent.left;
    owns parent.right;
    ensures parent.left == 8;
    ensures parent.right == old(parent.right);
    ensures result == 8;
} by {
    execute();
    simp();
}

fn shared_field(parent: &mut Pair) -> i32 {
    owns parent.left;
    views parent.right;
    ensures parent.left == 7;
    ensures result == old(parent.right);
} by {
    execute();
    simp();
}
```

A slice parameter, `&[T]` or `&mut [T]` with a scalar element, is one name.
`bytes.len()` is its length, `*bytes` is the whole slice, and its elements
and ranges are indexed as a pointer's are. An index or a range bound keeps
its `usize` type, so nothing is cast and the contract states no bound on the
length:

<!-- verified-example: tests/fixtures/rust-verification/slices.click -->
```click
verifying "borrow.rs";

fn length(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
} by { execute(); simp(); }

fn read(bytes: &[u8], index: usize) -> u8 {
    requires index < bytes.len();
    views *bytes;
    ensures result == bytes[index];
} by { execute(); simp(); }

fn write(bytes: &mut [u8], index: usize, value: u8) {
    requires index < bytes.len();
    owns *bytes;
    ensures bytes[index] == value;
} by { execute(); simp(); }

fn first(bytes: &[u8]) -> u8 {
    requires bytes.len() == 4u64;
    views bytes[0..4];
    ensures result == bytes[0];
} by { execute(); simp(); }

fn increment_first(bytes: &mut [u8]) {
    requires bytes.len() == 4u64;
    requires bytes[0] < 255;
    owns bytes[0..4];
    ensures bytes[0] == old(bytes[0]) + 1;
} by { execute(); simp(); }

fn empty(bytes: &[u8]) -> bool {
    ensures result == (if bytes.len() == 0u64 { 1 } else { 0 });
} by {
    if bytes.len() == 0u64 { execute(); simp(); }
    else { execute(); simp(); }
}
```

A method's contract is written in an `impl` block, `impl Type { ... }` or
`impl Trait for Type { ... }`, and its receiver is `self`, `&self` or
`&mut self`. It is the contract of the function the importer calls
`Type_name`. A trait with a type argument names its methods by that argument
too, as the importer does: the method of `impl MulAssign<u32> for Lanes` is
`Lanes_mul_assign_u32`, and of `impl AddAssign<&Lanes> for Lanes`,
`Lanes_add_assign_ref_Lanes`.

An item of a crate import is named by its path from the crate:
`fn quad::walk(bytes: &[u8]) -> u32`, a type `quad::Quad`, and
`impl adler2::algo::U32X4 { ... }`. The path stands for the name the
importer gives the item (`__rust_q_I4_quad_I4_walk`). A diagnostic prints
the path, `quad::walk.contract`, and `--claim` and `--trace-proof` take it.
An operator-trait method prints in Rust's qualified form: the method of
`impl MulAssign<u32> for adler2::algo::U32X4` is
`<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign`, a reference or by-value
argument reads `<T as AddAssign<&T>>::add_assign` or
`<T as AddAssign<T>>::add_assign`, and `impl Default for adler2::Adler32` is
`<adler2::Adler32 as Default>::default`. `--claim` and `--trace-proof` take
that form, the importer's name, or a `FILE:LINE` location in the sidecar
([claim labels](cli/expand.md#claim-labels)). The importer names an inherent method by the
module its `impl` block is in, which Rust does not write: the method is
found in the import by its type and name, of which Rust allows one.

<!-- verified-example: tests/fixtures/rust-verification/impl_blocks.click -->
```click
verifying "borrow.rs";

impl Drop for Guard {
    fn drop(&mut self) {
        requires separate(memory(*self), memory(self.slot[0..1]));
        owns self.slot;
        owns self.saved;
        owns *self.slot;
        ensures self.slot == old(self.slot);
        ensures self.saved == old(self.saved);
        ensures *self.slot == old(self.saved);
    } by {
        execute();
        simp();
    }
}

fn cleanup(value: &mut i32) {
    owns *value;
    ensures *value == 42;
} by {
    execute();
    simp();
}
```

A reference to an array, `&[T; N]` or `&mut [T; N]` with a scalar element,
is the pointer to its first element. The length is the type's, so the
contract writes it, `views bytes[0..4]`
([`examples/rust-array-slices`](https://github.com/clicklang/click/blob/master/examples/rust-array-slices/arrays.click)).

A signature the importer cannot lower is refused in the sidecar too: an
array or slice by value, a reference to a reference or to `()`, and a slice
or array whose element is not a scalar. `fn` in a C or C++ sidecar is
refused. Click's own words (`requires`, `ensures`, `owns`, `result`, the
tactics) are the same in every language.

## Supported semantics

The scalar slice supports `i32`, `u8`, `u16`, `u32`, target-sized `usize`, booleans, unit returns, initialized scalar
and reference locals, branches, direct calls within the selected file,
references to `i32`, `u8`, `u16`, and `u32`, and plain structs with those integers or reference fields, field
access, and local reborrowing of reference-backed places. Arithmetic supports addition,
subtraction, multiplication, division, remainder, bitwise operations, comparisons,
and boolean operations. Unsigned shifts support `u8`, `u16`, `u32`, and `usize`; signed shifts
remain unsupported. Integer `as` casts preserve Rust truncation and bit
interpretation. Record
size, alignment, and field offsets come from rustc for the selected target;
Rust's default field order is not assumed.

Single-file imports (schema 3) use Rust 2024; crate imports (schema 4) select
2021 or 2024. The rest of the fixed profile is compiler commit
`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, target
`x86_64-unknown-linux-gnu`, overflow checks enabled, panic abort, and MIR optimization level zero. Click must
prove that arithmetic overflow does not occur. Compiler acceptance alone does
not prove a functional claim or panic freedom.

Unsigned arithmetic has Rust's checked semantics: addition, subtraction, and
multiplication require overflow freedom, and division/remainder require a
nonzero divisor. A shift count must be nonnegative and less than the left
operand's width (8, 16, 32, or 64); shifting away high bits is allowed. Casts to `u8` and `u16`
retain the low eight and sixteen bits, respectively. Checks follow operand evaluation order and respect
`&&`/`||` short circuiting. Compound assignments use the same operations.
These obligations are checked during execution; C unsigned wrapping alone
cannot establish Rust panic freedom.

[`examples/rust-unsigned/arithmetic.rs`](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.rs)
is a synthetic scalar regression covering byte accumulation, multiplication,
modular reduction, shifts, packing, truncation, and unsigned comparison. Its
[sidecar](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.click)
uses ordinary Click contracts and tactics. Expansion can use the shared
`unsigned_sum_bound` arithmetic-certificate step for widened word bounds.
The [unchanged Adler2 computation](https://github.com/clicklang/click/blob/master/design/charon-trial/adler2/README.md)
is verified separately against the common checksum specification for lengths
zero through 2,147,483,647 bytes from canonical initial states. The unchanged
`write_slice` and `adler32_slice` wrappers compose checked bodies over the same
range, preserve input bytes, and prove field and packed checksum correctness.
A locked client also proves that two actual updates equal the full-input
checksum for every valid split over that range. Saved-checksum restoration
and resumed updates remain pending.

```sh
cargo run --bin click -- import lock examples/rust-unsigned/arithmetic.click
cargo run --bin click -- verify examples/rust-unsigned/arithmetic.click
```

## Byte slices and indexing

Shared `&[u8]` and mutable `&mut [u8]` parameters, local copies and reborrows,
builtin `.len()`, indexed reads and writes, and direct slice calls are supported.
Slice references lower to paired parameters: `bytes: &[u8]` becomes
`const uint8* bytes, uint64 bytes_len`; a mutable slice uses `uint8*`.
The generated `<parameter>_len` name must not collide with another parameter.
On the pinned target, `usize` is a 64-bit unsigned value, including lengths,
index literals, comparisons, casts, returns, and general scalar arithmetic.
Addition, subtraction, and multiplication require checked overflow freedom at
the full 64-bit width; division/remainder require a nonzero divisor. Bitwise
operations, checked shifts, and scalar compound assignments are supported.
Casts to `u32`/`i32` retain the low 32 bits, casts to `u8` retain the low eight
bits, and `i32 as usize` sign-extends before interpreting the bits as unsigned.
See [`examples/rust-usize`](https://github.com/clicklang/click/tree/master/examples/rust-usize)
for contracts over arithmetic, casts, computed indices, and length increments.

Every index checks `index < length` at the full target width before address
formation. Shared reads require `views`; writes require `owns`. Local slice
copies and calls preserve both pointer and length. The compiler checks borrow
legality; Click checks memory authority and the indexed values.

The [byte-slice example](https://github.com/clicklang/click/blob/master/examples/rust-slices/bytes.click)
uses variable-length contracts with existing memory ranges, as `read` and
`write` in "Signatures in Rust syntax" do. A range bounded by a `usize` has 64-bit bounds, so the contract states no
limit on the length. `.len()` alone needs no byte resource. General slice returns, range subscripts, indexed compound assignment, and
other slice element types remain unsupported. Supported shared slice splitting
is described below. Normal numeric contract casts now include
`(int32)`, `(uint32)`, `(int64)`, and `(uint64)`.
Use signed 64-bit widening to state full-width u32 addition guards, for
example `((int64)x + (int64)y) <= 4294967295i64`.

## Shared slice splitting

The standard shared byte-slice method supports local destructuring:
`let (left, right) = bytes.split_at(mid)`. The exporter checks the resolved
core slice method and retains a `SliceSplit` operation. The receiver must be
a local `&[u8]`; both tuple elements must be plain bindings. General tuple
values, wildcard patterns, direct array receivers, mutable slice receivers,
and `split_at_mut` remain unsupported.

The receiver's pointer and length are captured before evaluating the midpoint,
which is evaluated once. Execution checks `mid <= bytes_len` at the full
64-bit `usize` width. The left slice keeps the original pointer and length
`mid`; the right starts at `bytes + mid` and has length `bytes_len - mid`.
No bytes are copied and no write authority is created. Subsequent reads use
the original input's `views` authority; the compiler rejects writes through
either shared result. Both results work with existing slice aliases,
indexing, `.len()`, and direct slice calls.

Pointer formation currently requires a checked `mid <= INT32_MAX` bound,
before narrowing the offset into the shared memory model. The original and
result lengths retain all 64 bits: metadata-only contracts can use larger
lengths when the midpoint fits. Splitting at zero or at the length is valid,
including an empty input; reading an empty result still fails its index check.

The [split fixture](https://github.com/clicklang/click/tree/master/examples/rust-split-at)
proves both result lengths and reads through each slice for variable split
points. Its regressions cover endpoints, full-width lengths and invalid split
indices, missing read authority, false values, and expanded proofs.

## Fixed arrays, copies, and checked indexing

Shared `&[T; N]` and mutable `&mut [T; N]` parameters support `u8`, `u32`,
and `i32` elements with concrete, compiler-evaluated lengths. A fixed-array
reference lowers to a typed pointer without a separate length parameter:
`&[u32; 3]` becomes `const uint32*`. The length remains in the prepared
execution and every indexed read, write, or element borrow checks
`index < N` at the full 64-bit `usize` width before forming an address.
Typed pointer arithmetic preserves element widths; word indices do not become
byte offsets. Array storage must fit the current signed-word memory model
(`N * sizeof(T) <= INT32_MAX`).

Compiler storage starts for local scalar arrays create checked fresh backing at
that point, including inside symbolic iterator loops. Plain record storage
starts also restore backing for array-field snapshot copies. The loop contract
need not list compiler-created local arrays as input resources. Re-entry checks
live loans and replaces the previous object's identity; initialization and
complete source/destination copy authority remain required.

Builtin `.len()`, local reference aliases and reborrows, and direct fixed-array
reference calls are supported. `.len()` requires no memory authority, including
for zero-length arrays. Reading any element of a zero-length array cannot pass
the checked panic obligation. Reads require `views` or `owns`, and writes
require `owns`; Rust reference types do not supply these resources implicitly.
The compiler checks conflicting borrows, while Click rejects false functional
claims and contracts that fail to establish bounds or memory authority.

The synthetic [fixed-array example](https://github.com/clicklang/click/blob/master/examples/rust-arrays/arrays.click)
covers all three element types, a checked element reborrow, a direct helper
call, parent reuse, and preservation of an untouched word. Its helper owns
only the indexed word, allowing the caller to retain the remaining storage.

```sh
scripts/build-charon.sh --install-toolchain
cargo run --bin click -- import lock examples/rust-arrays/arrays.click
cargo run --bin click -- verify examples/rust-arrays/arrays.click
cargo run --bin click -- audit examples/rust-arrays/arrays.click
```

Initialized local arrays support literals (`[3u32, 5]`), repeats (`[value; 4]`),
and whole-array copies (`let copied = original`, `words = replacement`,
`*target = *source`). Each local has independent automatic storage. Constructor
operands are evaluated in source order before writing the destination; a repeat
operand is evaluated once, even when its length is zero. Copies capture all
source elements before writing and require read authority over the entire
source and write authority over the entire destination. Local arrays can be
borrowed, indexed, and passed to fixed-array reference parameters.

The synthetic [array-values example](https://github.com/clicklang/click/blob/master/examples/rust-array-values/arrays.click)
checks independent copies, replacing an array from its own elements, copies
through references, empty arrays, and constructor calls with observable effects.

Fixed byte arrays coerce to `&[u8]` and `&mut [u8]` in local initialization,
slice reassignment, and direct calls. The slice points at the original array
and carries its fixed length as 64-bit metadata; coercion allocates no storage
and grants no memory authority. Mutable sources can also coerce to shared
slices. Zero-length arrays support length-only calls without memory authority.
The compiler checks borrow validity, and Click still checks slice bounds and
the callee's `views`/`owns` requirements. See the synthetic
[array-to-slice example](https://github.com/clicklang/click/blob/master/examples/rust-array-slices/arrays.click).

By-value array parameters or returns, nested arrays, and non-byte slices
remain unsupported. Supported flat records can contain owned array fields,
including in schema-4 record returns described above. Indexed compound
assignment remains outside the supported subset. The builtin length
operation also supports non-byte fixed arrays by recovering their fixed
length; this does not enable non-byte slices or general library methods.

Schema-3 single-file imports exclude modules and imports; schema 4 supports
the locked module closure described above. Macros, semantic attributes,
dependencies, unsafe code, general traits, type/const generics, heap
allocation, nested aggregate parameters, reference returns, and other integer widths
are outside this slice. Unsupported syntax
fails during extraction or direct lowering. This is not general Cargo-project
support.

## While loops and invariants

Unlabeled `while` loops, including nested loops, use the shared checked loop
rules. Sidecars can declare `invariant`, memory/resource clauses, and numeric
`decreases` measures. Entry and preservation are separate obligations;
arithmetic and indexing in the body retain Rust's panic-freedom checks.
A decreasing measure proves termination through the existing loop checker.
Charon locals with unique source names use those names in sidecars. Unnamed
and ambiguous locals use collision-checked `__rust_mir_ID` identities from the
locked artifact. These compiler identities can change when the artifact is refreshed.

Conditions currently support scalar comparisons, boolean combinations,
negation, casts, and builtin `.len()`. Calls, indexing, and arithmetic in a
condition require repeated preparation of checked operands and are rejected.
General iterators, `loop`, labels, `break`, and `continue` remain unsupported.
The copied-byte slice `for` form described below is supported.

[`examples/rust-loops/loops.rs`](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.rs)
and its [sidecar](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.click)
verify a scalar counter, checked accumulation, and a byte-slice walk with a
full-width `usize` counter. The walk uses `invariant i <= bytes_len` and
`decreases bytes_len - i`; slice access requires `views` authority.
Full-width range endpoints retain the target’s `usize` width; contracts using
signed indices must separately justify their conversions. The accumulator contract fixes the added value
to one. These are synthetic loop regressions, not a checksum-library proof.
Verification, profiling, auditing, and proof expansion use the shared engine.

```sh
cargo run --bin click -- import lock examples/rust-loops/loops.click
cargo run --bin click -- verify examples/rust-loops/loops.click
```

The [byte-sum example](https://github.com/clicklang/click/blob/master/examples/rust-byte-sum/sum.click)
proves a functional loop over arbitrary input bytes. For slices of length
`0..=1000`, its unchanged Rust source returns the exact mathematical sum of
the input at function entry. A prefix fold and the bound
`0 <= to_integer(total) <= 255 * to_integer((int32)(uint32)i)` establish the
result and safety of every intermediate addition. Checked full-width bounds
connect the `usize` counter to the fold's signed-word endpoint. It covers
empty input and supports profiling, audit, and expanded-proof reverification.

## Slice iterator loops

`for &byte in bytes`, `for byte in bytes`, and either pattern over
`bytes.iter()` support an immutable binding of type `&[u8]`.
The pinned compiler resolves `IntoIterator::into_iter` and `Iterator::next`;
the exporter checks their identities and the compiler's `Option` match before
lowering the loop. The `.iter()` method must resolve to the standard core
inherent slice method. Copied patterns read each yielded byte into a `u8`
binding; reference patterns bind a shared `&u8` address whose dereferences
require view authority. Shared-reference qualifiers survive local declarations.
The original Rust source stays unchanged.

The adapter retains Charon's native control flow, iterator calls, and `Option`
branches. A shared iterator named `iter` exposes `iter_cursor`,
`iter_remaining`, and `iter_live`; unnamed or ambiguous iterators use their
`__rust_mir_ID` identity as the prefix. A successful `next()` records the
shared element address in the returned option, advances the cursor, and
reduces the remaining length before entering the Rust body. Copied patterns
read that address; reference patterns bind it directly. An exhausted iterator
exits without a read or pointer advance, including for an empty slice.

There is no generated processed-count or index variable. Sidecars choose their
own properties of iterator state. The sum examples explicitly relate the cursor
to the original slice and derive a processed prefix as original length minus
remaining length; the remaining length also proves termination. This length is
the iterator's remaining slice metadata, represented as full-width `uint64`
for the locked 64-bit target. Signed prefix-index observations require a checked
range and conversion in the sidecar. Reads require view authority and
body arithmetic retains its panic checks. Immutable slice bindings keep the
original pointer and length stable; mutable bindings and slices are rejected.

[`examples/rust-iterators/sum.rs`](https://github.com/clicklang/click/blob/master/examples/rust-iterators/sum.rs)
and its sidecar prove the same exact byte sum as the `while` example for arbitrary
bytes and lengths `0..=1000`. Verification, profiling, audit, and expanded-proof
verification have regressions. The
[reference iterator fixture](https://github.com/clicklang/click/blob/master/examples/rust-iter-references/sum.rs)
proves the same sum using `for byte in bytes.iter()` and `*byte`. Missing views
and attempts to write through yielded shared references are rejected.
Shared iteration over fixed `i32`, `u8`, and `u32` arrays is also supported,
including borrowed arrays, local arrays, explicit `.iter()` calls, stored
`Iter` locals, and moves of the remaining iterator. See the locked
[array iteration trial](https://github.com/clicklang/click/tree/master/design/charon-trial/array-iteration).
Moving an iterator retires its source; repeated exhaustion yields no element.
`.iter_mut()`, by-value array iteration, custom iterators, labels, `break`, and
`continue` remain outside this subset.

## Primitive unsigned conversions

Calls such as `u32::from(byte)` and `<u32 as From<u16>>::from(half)` support
compiler-resolved core `From` conversions between modeled unsigned scalar
types (`u8`, `u16`, `u32`, `usize`) when the source width is no greater than
the destination width. The Charon adapter validates the selected core
implementation, signature, and concrete types before constructing Click's
`IntegerFrom` operation;
lowering preserves the value and evaluates its argument once in source order.
These pinned standard-library primitive conversions are interpreted builtins;
their library bodies are not imported. Matching a method's spelling alone does
not authorize a conversion. User conversion implementations, `.into()`, bool
conversions, and general trait dispatch remain unsupported. The same adapter
rule applies inside supported owned-record functions.

`u16` has checked arithmetic, scalar references, and compiler-layout record
fields with two-byte storage. It does not extend the supported fixed-array
element or slice types. The
[integer-conversion fixture](https://github.com/clicklang/click/tree/master/examples/rust-integer-conversions)
checks shared reads, exclusive updates, preserved neighboring fields, and a
fixed checksum-style accumulator boundary case. It does not verify arbitrary
checksum updates or import adler2.

## Exact chunk iterators and remainder

The core shared byte-slice `chunks_exact(size)` method supports stored local
iterators, `for chunk in chunks`, `for chunk in &mut chunks`, and direct or
nested `for chunk in bytes.chunks_exact(size)` loops. The exporter checks the
resolved core slice method, the concrete `ChunksExact<u8>` type, and the
compiler's standard iterator/Option desugaring. It retains `ChunkDeclare`
and `ChunkFor` operations. `chunks.remainder()` checks the resolved core
inherent method and retains a `ChunkRemainder` expression. The receiver is
a shared byte-slice local; parameters or returns of iterator type, iterator
assignment/copying, adapters, and explicit `next()` calls are unsupported.

Construction captures the receiver before evaluating the size once, then
checks `size != 0`. Input lengths retain the locked target’s `usize` width.
For an iterator named `chunks`, the sidecar sees `chunks_cursor`,
`chunks_remaining`, `chunks_size`, `chunks_tail`, and `chunks_tail_len`.
The complete range has length `length - length % size`; its cursor initially
points at the original input. The fixed tail begins at the end of that
range and has length `length % size`. Chunk sizes and tail lengths retain
64 bits, as does the complete range's remaining length. The iterator does not
truncate metadata or impose an artificial `i32::MAX` construction limit.
Sidecars that express prefixes with signed indices must prove the relevant
range and value-preserving conversions.

Each successful `next` binds a shared byte subslice of length `size`, then
advances the cursor and subtracts that size from the remaining complete
range before the source body runs. The exhausted case performs no reads or
pointer advance. `remainder()` exposes the fixed tail, independently of how
many complete chunks were consumed. A saved remainder can be used after
consumption by value; borrowing the iterator allows subsequent method calls.
The compiler enforces moves and borrows. Neither method copies bytes or
creates write authority. Reads through chunks, aliases, calls, and tails
retain the original input's view requirements.

The [exact-chunk fixture](https://github.com/clicklang/click/tree/master/examples/rust-chunks-exact)
uses a cursor invariant and a divisibility invariant to describe the input
partition without a generated processed count. Regressions cover empty
input, exact multiples, short tails, nested loops, full-width chunk sizes,
zero-size rejection, false claims, missing bounds/views, and expanded proofs.
Mutable chunk iterators and non-byte slices remain unsupported.

## Moves and drops

[`examples/rust-move-drop/guard.rs`](https://github.com/clicklang/click/blob/master/examples/rust-move-drop/guard.rs)
constructs a guard, moves it, changes borrowed storage, and returns through two
paths. Its checked `Drop` contract restores the original storage value. The
caller proves the result was captured before cleanup and that the storage was
restored on both paths.

Local non-Copy structs support whole-value construction and moves, scope and
early-return cleanup, conditional initialization/moves, and explicit
`std::mem::drop`. Structs can have lifetime parameters and a local `Drop`
implementation. The compiler selects drop order and drop flags through its
ULLBC control flow; Click does not reconstruct cleanup
from source scopes. Destructor bodies require verified sidecar contracts.

Private checked live flags require a live source and dead destination for a
move, and consume the source. Reads and drops require a live value. Cleanup
must consume every destructor-bearing local before return. The flags prevent
stale struct bytes from justifying duplicate moves, duplicate drops, or omitted
cleanup. Struct storage uses existing checked stack allocation and typed field
loads/stores. Moving a reference field carries the same borrowed address; it
does not create allocation or deallocation authority.

Borrowing fields of local owned structs is supported. In
[`examples/rust-field-borrow/guard.rs`](https://github.com/clicklang/click/blob/master/examples/rust-field-borrow/guard.rs),
a child guard borrows its parent's saved field. Its destructor writes 42 to
that field, and the parent's destructor subsequently writes 42 to the caller.
Existing `owns` contracts suffice: the checked call planner consumes the
returned field owner and the retained storage fragments to supply the next
call. Each actual supplier is consumed once; views and gaps cannot supply
ownership. Regressions also cover parent mutation after explicit child drop,
disjoint mutable field borrows, false final-value claims, and compiler rejection
of conflicting parent access and use after move. The example passes verification,
profiling, audit, expansion, and re-verification without new Click syntax.

rustc establishes source borrow legality. These checks do not yet extract a
complete Rust loan protocol or infer ownership contracts from Rust types.

The adapter supports moving a reference field out of a plain local struct.
It still excludes general partial moves with cleanup, nested owned fields,
nested aggregate arguments or returns, unstructured control flow, heap owners such
as `Box`/`Vec`, and panic unwinding. Arithmetic, owned values, and loops use the
same native body representation; there is no whole-function coverage switch.

```sh
cargo run --bin click -- import lock examples/rust-move-drop/guard.click
cargo run --bin click -- verify examples/rust-move-drop/guard.click
cargo run --bin click -- import lock examples/rust-field-borrow/guard.click
cargo run --bin click -- verify examples/rust-field-borrow/guard.click
```

## Borrow and proof boundary

rustc establishes source type and borrow legality. Click checks the functional
contract and memory access obligations of the extracted execution. `&mut T`
parameters use pointer-shaped sidecar parameters with explicit `owns` clauses;
shared references use explicit `views` where access is required. Borrowed
references carry no allocation or deallocation authority.

This frontend does not infer sidecar authority from a Rust reference. Contracts
must provide the resources they use. Reborrows of caller storage retain the
same modeled pointer: writes through the child are observed through its parent.
The compiler establishes when parent reuse is legal; the kernel establishes
that each modeled access is justified by the supplied resources. Explicit
resource suspension/recovery remains roadmap work.

The trusted boundary includes the pinned compiler, exporter, semantic artifact,
and its translator. The lock detects stale or changed inputs; it is not an
attestation against somebody deliberately replacing the artifact and its lock.
Tests distinguish invalid Rust rejected by rustc from false functional claims
rejected by Click, and check the ordinary CLI and proof expansion path.
