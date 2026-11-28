# Experimental Rust imports

Click accepts a small safe, monomorphic subset of Rust 2021 and 2024. Its Rust importer
uses pinned, unmodified [Charon](https://github.com/AeneasVerif/charon) after rustc
type and borrow checking. Every imported body follows the native ULLBC control
flow path into Click's shared execution, memory, and certificate rules.
Verification uses the same sidecars, tactics, and bounded engine as C and C++.
[Language coverage](coverage.md) compares the Rust subset with C and C++.

Charon is the extraction backend. On `x86_64-unknown-linux-gnu`, releases provide
an optional pinned frontend and compiler runtime through
`click add rust`. Rust support remains experimental and covers
the subset listed in [Language coverage](coverage.md). Contributor builds use
`scripts/build-charon.sh`; ordinary verification of committed locks needs
neither Charon nor rustc.

The working example is
[`examples/basic-rust/borrow.rs`](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.rs),
with its
[sidecar](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.click).
It covers a scalar branch, a mutable reference helper that writes through a
local reborrow and then reuses its parent, and a caller proving a struct field's
final value while preserving its other field. A shared field borrow remains
stable while the disjoint field is mutated.

## Installed Rust frontend

`click add rust` installs a bundle at
`CLICK_HOME/versions/VERSION/frontends/rust` (with the usual default
`CLICK_HOME`). The bundle's bounded `frontend.json` explicitly identifies
Charon, its paired driver, rustc, and the sysroot. Extraction checks the running
Click version, pinned Charon version/revision, compiler commit and host before
compiling. The Charon wrapper's paired-driver layout is validated against the
explicit driver entry. The bundle supplies its own target libraries and loader
paths; installed extraction does not search for rustup or use ambient compiler
flags. A missing bundle names `click add rust`. A mismatched or
incomplete installed bundle names its exact frontend path to remove before
reinstalling: ordinary installation retains an existing bundle. Version errors
show the expected identity and the bounded identity actually reported. A
`CLICK_CHARON` override instead points to correcting/unsetting that override
and the source-build setup command. Hosts without a packaged bundle are
reported as unavailable rather than being given an install command that
cannot supply their platform.
The Rust front end currently ships a Linux x86-64 GNU bundle.

Rust project units use this frontend automatically. `CLICK_CHARON` is a
contributor override: a bundle directory selects that bundle, while an
executable selects the existing source-build path and its rustup-managed pinned
toolchain. The project schema and lock format are described
in [`click capture`](cli/capture.md#project-units) and
[project configuration](../concepts/own-project.md).

The release workflow builds Charon with `scripts/build-charon.sh --release`
and assembles the bundle with `scripts/package-rust-frontend.py`, including its
compiler libraries and license files. The installed-layout regression relocates
that bundle and an installed Click, extracts and verifies the unchanged basic
Rust example with crate-qualified sidecar names and the existing adler2
saved-checksum proof, repeats locking byte-for-byte,
checks mismatched identity refusal, then verifies after removing the frontend.

A separate release-packaging check consumes the exact archive and checksum
produced by `scripts/package-rust-frontend-archive.sh`. It starts with only a
Click launcher, invokes the real `click add rust` command using
local release assets through its ordinary curl subprocess, relocates the
installed home, and verifies the basic Rust example with an empty PATH and no
user Rust toolchain. It checks repeated installation and locking, then offline
verification after removing the frontend. The
[C/Rust checksum demonstration](https://github.com/clicklang/click/blob/master/design/adler32/project/checksum-correspondence.md#reproduce)
is checked from a relocated prepared directory by a nightly test instead. The
release workflow runs the packaging check
before attaching assets to a release and on pull requests touching packaging.
The dedicated integration target stays outside the normal ten-minute gate;
there is no development-binary fallback for its release archive.

## Reproduce the example

Run `scripts/setup-environment.sh` once for Click's pinned stable toolchain.
Build pinned Charon and install its separate compiler with
`scripts/build-charon.sh --install-toolchain`, then run:

```console
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
cargo run --bin click -- profile examples/basic-rust/borrow.click
cargo run --bin click -- audit examples/basic-rust/borrow.click
cargo run --bin click -- expand --claim update.contract --in-place examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

Locked Rust imports also support focused proof tracing:

```console
cargo run --bin click -- verify --trace-proof update examples/basic-rust/borrow.click
```

Use a function or theorem name declared in the sidecar. `--trace-to LINE[:COLUMN]`
selects a written tactic within that proof. Only the named proof is checked;
other function contracts remain interfaces. Tracing validates the ordinary
import lock and does not rerun the compiler.

Every Rust example is a project: its `click.project.json` declares one Rust
unit per source, and a sidecar selects a unit with its ordinary `verifying`
path. A unit without a `crate` object is one `.rs` file compiled as a Rust 2024
library, with no other inputs:

```json
{"units": {"borrow": {"language": "rust", "sources": {"borrow.rs": {}}}}}
```

`click capture` runs the compiler with a bounded process and writes
`.click/captures/<unit>/<source>.ullbc` and `.click/captures/manifest.json`. Ordinary
verification loads those files without executing the compiler. Source, unit
description, artifact, or profile changes require refresh, and a changed
source is named. The lock includes the compiler/extractor identity; after
updating the extractor or adapter semantics, refresh existing imports. The
normal example gate checks locked native inputs offline, while the nightly
gate's live Charon tests refresh and verify all 16 original Rust fixtures.

A Rust unit's lock entry uses the envelope shared with C and C++, and its
import identity the shared formula ([import.md](cli/capture.md)); the `rust`
section records the lock schema, the source and the front end. Legacy
configurations still accept `"charon-trial"` as a backend compatibility alias.
Historical single-file crate/output labels inside serialized artifacts remain
stable.

Rust lock schema 9 records `frontend`: the Click release version, pinned Charon
version/revision, rustc commit and a SHA-256 identity of the complete extraction
and semantic profile. The front end's `identity` is the SHA-256 of that record,
so the import identity binds it to the unit, source closure and artifact. Local executable bytes, runtime paths and host
installation directories are absent. Source-built overrides use the same pins
and runtime handshakes, so equal inputs and extraction output give the same lock
as the packaged release. Extraction still detects executable changes during a
run. Single-file artifact source paths are normalized to their source filename;
crate paths remain relative to the unit root.

A schema-8 section, from releases before the `frontend` record, names the
exporter and Charon driver digests and the semantic profile it was prepared
under; it loads only while that profile is current. `click capture`
refreshes it into schema 9; a Click release or semantic-profile change also
requires refresh. Normal verification never rewrites a lock.

## Locked crates and qualified declarations

A unit with a `crate` object gives an explicit crate root and compiler
configuration:

```json
"adler2": {
  "language": "rust",
  "sources": {"src/lib.rs": {}},
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
appear exactly once in `files`. rustc dep-info checks that closure. A mismatch lists missing entries in
`crate.files` and extra configured entries, with bounded lists. If a module or
include is omitted, rustc may fail before emitting dep-info because only the
configured files are copied into the private compiler state. That error
retains rustc's filename/module diagnostic and explains how to check
`crate.files`; it never expands the compiler state implicitly. Files must
be regular, use normalized relative paths, and stay inside the unit root without symlinks. Environment-dependent source macros are rejected.


Extraction compiles a private state of those bytes. The aggregate source
hash covers every input, and configuration hashes bind the root, edition,
features, and entry points. Ordinary loading rechecks the full closure
without executing a compiler. Crate artifacts use the versioned
`click-charon-crate-v4` envelope; single-file units keep the earlier identity.

Module definitions and inherent methods retain compiler-resolved identities.
Proof identifiers encode tagged, length-prefixed path components, so `a::read`,
`b::read`, and `a_read` remain distinct even when their leaf names overlap.
Inherent methods include their resolved receiver type. Calls still follow
Charon's declaration IDs and execute imported bodies; names never grant a
library summary. Concrete assignment operators retain their trait,
implementation, signature, and associated-item checks across module paths.

Crate units support by-value returns of supported flat records, including owned
array fields and records with `Drop`. The concrete return layout enters the
kernel's aggregate-return interface: field values copy into fresh caller
storage. Reference, array, and
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

Crate units import local named scalar constants (`bool`, `i32`, `u8`, `u16`,
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

The unchanged adler2 example proves `Adler32::default` and `Adler32::new` return
`a = 1`, `b = 0`. Concrete assignment operators also accept supported
by-value record operands through the checked call interface. Selecting the
complete checksum loop now produces a locked, prepared import, and its
`MOD` and `CHUNK_SIZE` initializer contracts verify. Its unchanged whole body
proves bounds, termination, and both final checksum fields against the common
specification for canonical seeds and every slice length, including full
batches and both remainders. General trait dispatch and arbitrary Rust
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
}

fn times_three(value: u32) -> u32 {
    requires value <= 1431655765u32;
    ensures result == value * 3u32;
}

fn reduce(value: u32) -> u32 {
    ensures result == value % 65521u32;
}
```

A Rust source's function contracts require this form. A C-shaped signature
is refused with a suggestion of the `fn` form. A field through a
reference is `p.f`; `p->f` is refused. The
sidecar parser accepts every Rust integer and float type name, `bool`, `()`,
and a struct by name, but the importer admits only the types in
[Supported semantics](#supported-semantics); `usize` and `isize` are 64 bits. `expr as T` takes a
scalar type and binds as in Rust, tighter than a binary operator.

A parameter may be a reference, `&T` or `&mut T`, to a scalar or a struct.
The contract names what it refers to as Rust does: `*value` for the
referent and `parent.left` for a field. The type grants the authority a
safe caller holds, with no clause written:

- `value: &mut T` owns `*value` and `value: &T` views it, for a scalar, an
  `Option` of one, a crate enum, or a struct whose fields are scalars or
  such structs; an inherent method's `&mut self` and `&self` do the same for
  the `impl` block's type;
- a slice `bytes: &mut [T]` or `bytes: &[T]` owns or views
  `bytes[0..bytes.len()]`, and an array `bytes: &[T; N]` owns or views
  `bytes[0..N]`;
- a box moved in, `b: Box<R>` for such a struct `R`, consumes
  `allocation(b, sizeof(R))` and `*b`, and a box moved out, `-> Box<R>`,
  produces `allocation(result, sizeof(R))` and `*result`.

The derived clause is the one a sidecar would write, so the callee is checked
against it and each caller must hold it. A sidecar that writes an `owns`,
`views`, `consumes` or `produces` clause naming the parameter (or `result`)
states its authority itself, and nothing is derived for it: `views
parent.right` on a `&mut Pair` promises the caller the field is not written.
`owns` through a shared reference is refused. A trait method, a generic
function, an `extern` or `contract` declaration, an option of a box, a struct
holding a box, pointer or array, and any other type keep only their written
clauses.
Lifetimes may be written or
left out, `fn pick<'a>(value: &'a u32) -> u32`; the contract does not use
them. Type parameters are limited to the supported
[callable bounds](#function-pointers-and-named-contracts) and
[crate trait bounds](#trait-method-interfaces). A tuple struct's field is
named by its position, `self.0`.

A diagnostic about a function whose signature is written this way, and the
proof `click expand` writes for it, write its places the same way: a
slice's length `bytes.len()`, a cast `(x as u32)`, and a field through a
reference `p.field`.

<!-- verified-example: tests/fixtures/rust-verification/references.click -->
```click
verifying "borrow.rs";

fn choose(x: i32) -> i32 {
    requires 0 <= x;
    ensures result == (if x < 7 { x + 1 } else { 7 });
}

fn set_seven(value: &mut i32) {
    ensures *value == 8;
}

fn update(parent: &mut Pair) -> i32 {
    owns parent.left;
    owns parent.right;
    ensures parent.left == 8;
    ensures parent.right == old(parent.right);
    ensures result == 8;
}

fn shared_field(parent: &mut Pair) -> i32 {
    owns parent.left;
    views parent.right;
    ensures parent.left == 7;
    ensures result == old(parent.right);
}
```

A slice parameter, `&[T]` or `&mut [T]` with a scalar element, is one
value: its data pointer and its length. `bytes.len()` is its length,
`bytes.as_ptr()` its data pointer, `*bytes` is the whole slice, and its
elements and ranges are indexed through its data pointer, `bytes[i]` and
`bytes[a..b]`. Pointer arithmetic and pointer comparisons are written on the
data pointer, `bytes.as_ptr() + k`; on the bare name, which is the slice,
they are refused. A slice result, `-> &[T]`, `-> &mut [T]` or `-> &str`, is
one value too: the contract reads `result.len()`, `result.as_ptr()` and
`result[i]`, and a caller binds the result as one slice local
([`tests/fixtures/rust-verification/slice-returns`](https://github.com/clicklang/click/blob/master/tests/fixtures/rust-verification/slice-returns/returns.click)).
A proof reads a slice local where it was live,
`at(statement(0).exit, view.as_ptr())`, and its elements there at the
slice's element type: for `let view = bytes;`, `have
at(statement(0).exit, view[0]) == bytes[0];` is proved. A caller that
indexes a returned slice reads the argument's element: for `let view =
whole(bytes); view[0]`, `ensures result == bytes[0]` is proved.
A proof's own read through the returned slice at a recorded point, `have
at(statement(0).exit, view[0]) == bytes[0]`, is not yet related to
`bytes[0]`
([step 3c-i](https://github.com/clicklang/click/blob/master/design/rust-slice-values.md#plan)).
An index or a range bound keeps
its `usize` type, so nothing is cast and the contract states no bound on the
length:

<!-- verified-example: tests/fixtures/rust-verification/slices.click -->
```click
import click::integer;

verifying "borrow.rs";
theorem byte_reflexive(value: uint8) { ensures value == value by { close(); } }

fn length(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
}

fn read(bytes: &[u8], index: usize) -> u8 {
    requires index < bytes.len();
    views *bytes;
    ensures result == bytes[index];
}

fn write(bytes: &mut [u8], index: usize, value: u8) {
    requires index < bytes.len();
    owns *bytes;
    ensures bytes[index] == value;
}

fn first(bytes: &[u8]) -> u8 {
    requires bytes.len() == 4;
    views bytes[0..4];
    ensures result == bytes[0];
}

fn increment_first(bytes: &mut [u8]) {
    requires bytes.len() == 4;
    requires bytes[0] < 255;
    owns bytes[0..4];
    ensures bytes[0] == old(bytes[0]) + 1;
} by {
    step_until(function.exit);
    have to_integer(old(bytes[0])) < 255 by { close(); }
    apply(integer::lt_step_le(to_integer(old(bytes[0])), 255));
    have 0 <= to_integer(old(bytes[0])) + 1 by { close(); }
    apply(integer::to_uint8_round_trip(to_integer(old(bytes[0])) + 1));
    have bytes[0] == old(bytes[0]) + 1 by {
        apply(byte_reflexive(to_uint8(to_integer(old(bytes[0])) + 1)));
        close();
    }
    close();
}

fn empty(bytes: &[u8]) -> bool {
    ensures result == (bytes.len() == 0);
} by {
    if bytes.len() == 0 { step_until(function.exit); close(); }
    else { step_until(function.exit); close(); }
}
```

A `bool` result is a specification `bool`
([Booleans](language/index.md#booleans)): `ensures result;` claims it is
`true`, and, as in Rust, a parenthesized comparison is a `bool` value, so
`ensures result == (bytes.len() == 0);` states it exactly. Outside a
parenthesized operand a comparison remains a proposition, and a C or C++
sidecar keeps every comparison a proposition. A `bool` parameter is a claim
too: `ensures early implies result == 7;`. Rust has no cast to `bool`, so
`x as bool` is refused.

In the program, a Rust `bool` is Click's `Bool`. A comparison, `!`, `&&` or
`||` that produces a `bool` value is the condition it tests, with no path
split: `let c = a < b;` and `match o { Some(b) => !b, None => true }` need no
written case split, and `a != b` over two `bool`s is their logical
disequality. `b as u8` and `b as i32` are 1 when `b` holds and 0 otherwise.
`&bool` parameters and slices of `bool` are not supported.

### Integer literals

An unsuffixed literal takes its type from what it is compared or combined
with, so `bytes.len() == 4` compares two `usize` values. Rust sidecars accept
decimal literals and the Rust radix prefixes `0x`, `0o`, and `0b`. Underscore
separators are accepted in the digits and before a suffix, as in
`65_535u16`, `0xff_ff_u16`, and `0b1_010usize`.

A suffix fixes the literal's native type: `i8`, `i16`, `i32`, `i64`, `isize`,
`u8`, `u16`, `u32`, `u64`, or `usize`. On the pinned target, `isize` and
`usize` are 64 bits. These are specification integer types; imported source
coverage is defined under [Supported semantics](#supported-semantics).
Floating-point suffixes and 128-bit integer suffixes are not supported.

A suffixed literal must fit its type; it is never truncated to make it fit.
A signed minimum, such as `-2_147_483_648i32` or `-(0x8000_0000i32)`, is
accepted under unary minus. The same positive magnitude is out of range.
Negating an unsigned suffixed literal is refused. Unsuffixed literals retain
contextual typing, including arbitrary-precision mathematical `Integer`
values when no native type is required.

<!-- verified-example: tests/fixtures/rust-verification/integer_literals.click -->
```click
verifying "literals.rs";

theorem literal_forms(word: u16, index: usize, signed_word: i32) {
    requires word == 0xff_ff;
    requires index == 0b1_010;
    requires signed_word == -0x8000_0000;
    ensures word == 65_535u16 by { close(); }
    ensures index == 0o12usize by { close(); }
    ensures signed_word == -2_147_483_648i32 by { close(); }
}
```

### Pure functions, predicates and theorems

A Rust sidecar's pure functions, predicates and theorems, their quantifier
and `let` binders, and algebraic datatype fields take Rust types too: the
scalars (`u8`, `i32`, `u32`, `u64`, `usize`, `bool`, ...) and a raw pointer
to one or to a crate struct, `*const T` or `*mut T`. Such a function takes values, not borrows,
and a reference `&T` is refused there. `x as T` casts in a body as in a
contract. The C forms (`uint8`, `const uint8*`, `x as int32`) still read
the same types.

A pure function, predicate, theorem or contract may use Click's tuples,
`(u32, u32)`, `(a, b)` and `t.0`
([grammar](language/grammar.md#tuples)). A `fn` signature that takes or
returns a tuple is refused: tuple program values are not supported yet.

A pure function may take a slice of scalars, `bytes: &[u8]`. The body reads
`bytes[k]`, `bytes.len()` and `*bytes`. Each slice is one argument of a call:
a slice parameter in scope, such as a `fn`'s `bytes` or another pure
function's, that parameter at another point, `old(bytes)` or
`at(point, bytes)`, or a slice built from a pointer and a length,
`slice::from_raw_parts(p, n)` (with `import click::rust::slice;`), as a
theorem over `p: *const u8` and `n: usize` writes it. Passing the pointer and
the length as two arguments is refused. Printed proofs write a call the same
way, `size(old(bytes))`. The library's `Slice<T>`
(`library/rust/slice.click`) is the slice as one value, with `slice::len` and
`slice::as_ptr`; a `fn`'s slice parameter is that one value.

A slice in a value position is one `Slice<T>` value: the result of a pure
function, `fn half(bytes: &[u8]) -> &[u8]`, a type argument, `Option<&[u8]>`,
and an enum field, `Window(&[u8], usize)`. Rust's methods read it:
`half(bytes).len()`, `half(bytes)[i]` (a read under the caller's `views`) and
`half(bytes).as_ptr()`. They reduce without an `unfold` when the slice is
built, so `half(bytes).len() == bytes.len() / 2u64` closes by `close()`. A
slice value passes to a slice parameter as one argument,
`size(half(bytes))`. Failures print these forms, each reading back as
the same term: a written subslice as `bytes[1..3]` and its length as
`bytes[2..].len()`, a slice argument built from a pointer and a length as
`click::rust::slice::from_raw_parts(p, n)`. In a goal, a slice built as a
subslice prints as that subslice, `bytes[1..3]`: the kernel records it where
it is constructed, the same place its bounds are owed, so the printed form owes
nothing new when it is read back. A slice built any other way, such as the
body of `half` unfolded, prints as its construction,
`click::rust::slice::from_raw_parts(&bytes[1], 2u64)`. In a theorem
written in Click syntax, the library's calls print as calls,
`slice::len(slice::from_raw_parts(p, n))`. A slice is one built-in value,
a wide pointer holding its data pointer and its length, so `.len()` and
`.as_ptr()` of a constructed slice, such as a subslice, are its components
read in place, with nothing to unfold. A subslice,
`bytes[a..b]`, `bytes[a..]` or `bytes[..b]` of a slice parameter or a slice
value, is the slice value with data `bytes.as_ptr() + a` and length `b - a`
(`b` defaults to the length). It has no memory effect: `bytes[1..3][0]` reads
`bytes[1]` under the caller's `views`, and `bytes[1..3].len() == 2u64` closes
by `close()`. Its bounds are `usize`s, and they are Rust's: where Rust panics
unless `a <= b <= bytes.len()`, a subslice owes those bounds where it is
evaluated, as signed arithmetic owes its range. Under a guard, it owes them
only where the guard holds: `forall (k: usize) { k <= 2 implies ... bytes[k..2]
... }` owes `2 <= bytes.len()`, and the same claim without the guard is
refused. A bound the facts in scope do not establish is refused with its
condition, `not established: 5u64 <= bytes.len()`; establish it first, for
example `have half(bytes).len() == 2u64;` before `half(bytes)[1..]`. A
literal reversed range, `bytes[3..1]`, is refused as it is read. The
subslice is `slice::subslice(bytes, a, b)` from the
[slice library](library/index.md#slicesubslice). A method means what
its receiver's type says, however the receiver was introduced, so a slice
bound by a `match` arm, `Option::Some(s) => s.len()`, or by a `let`,
`let s = half(bytes); s[..1]`, reads with the same methods; a method the
type lacks is refused, "`Slice<uint8>` has no method `size`"
([methods](language/index.md#methods)). The
[byte-sum example](https://github.com/clicklang/click/blob/master/examples/rust-byte-sum/sum.click)
sums a prefix with `function prefix(bytes: &[u8], end: usize) -> Integer`,
whose body adds `to_integer(bytes[k] as i32)`, and calls it as
`prefix(bytes, i)`.

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
`<adler2::Adler32 as Default>::default`. A call step can name an inherent method of
a concrete generic type as `step(generic_stack::Stack::<u32>::push, { ... })`.
A crate trait is named by its path,
and its method's implementation prints as
`<trait_methods::Square as trait_methods::Shape>::area` ([trait method
interfaces](#trait-method-interfaces)). `--claim` and `--trace-proof` take
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
    }
}

fn cleanup(value: &mut i32) {
    owns *value;
    ensures *value == 42;
}
```

A reference to an array, `&[T; N]` or `&mut [T; N]` with a scalar element,
is the pointer to its first element. Its type supplies pointer formation
bounds through the array's one-past address, including when coerced to a slice.
Reading or writing elements still requires explicit authority, so the
contract writes the length in its resource, `views bytes[0..4]`
([`examples/rust-array-slices`](https://github.com/clicklang/click/blob/master/examples/rust-array-slices/arrays.click)).

A signature the importer cannot lower is refused in the sidecar too: an
array or slice by value, a reference to a reference or to `()`, and a slice
or array whose element is not a scalar. `fn` in a C or C++ sidecar is
refused. Click's own words (`requires`, `ensures`, `owns`, `result`, the
tactics) are the same in every language.

### Function pointers and named contracts

A sidecar callable parameter must match the source signature. A mismatch
reports both types in C syntax, such as `uint32 (*)(uint32)` against
`int32 (*)(int32)`.

A parameter of a safe Rust-ABI function-pointer type of scalar parameters and
a scalar or unit result, `f: fn(i32) -> i32`, is a callback, as in C. A named
contract is written as a Rust item, `contract fn Doubling(x: i32) -> i32 {
requires ...; ensures result == x + x; }`, and `requires Doubling(f);` gives
a call through `f` that contract, and a function passing its own `f` on
needs the contract too. Passing a function item, `apply(twice, x)`,
reifies it as a pointer; the caller's proof needs `twice` to meet the
contract, which Click checks at the call from `twice`'s own contract. When
the two contracts agree only by a proof, a refinement theorem shows it,
naming the crate function as a value by its path, as Rust passes it:
`theorem twice_is_doubling() { ensures Doubling(function_pointers::twice) by
{ unfold(Doubling(function_pointers::twice)); close(); } }`, and the caller's proof applies it,
`apply(twice_is_doubling());`. The diagnostic that refuses the call suggests
that theorem. The importer reads Charon's `CastKind::FnPtr` of a
crate function item and its `FnOperand::Dynamic` call through a local, and
refuses unsafe or foreign function pointers and pointers of non-scalar
parameters
([`design/charon-trial/function-pointers`](https://github.com/clicklang/click/blob/master/design/charon-trial/function-pointers/callback.click)).

A named contract's value parameter is written with a Rust type,
`contract fn Adds(x: i32) -> i32 { let amount: i32; ensures result == x +
amount; }`, and attached with `requires Adds(f, { amount: k });`, as in C
([`design/charon-trial/parameterized-contracts`](https://github.com/clicklang/click/blob/master/design/charon-trial/parameterized-contracts/adds.click)).

A closure that captures nothing can be passed for such a pointer,
`apply(|y| y + y, x)`. The sidecar selects the written closure expression in its enclosing function: `fn closures::caller.statement(0).call(0).argument(0)(y: i32) ->
i32 { requires ...; ensures ...; } by { ... }`, verified like any function,
and the caller's proof shows it meets the contract the callee requires of
the pointer. The path counts written calls and arguments from zero. A closure
directly in a local initializer uses `statement(i).initializer`. Parentheses
and a reference around a closure leave this selection on the same expression. The importer keeps the closure's `Fn::call` body, rewritten as
a function of the closure's parameters, and reads Charon's cast of the
generated `ClosureAsFn` function as the closure's address. A closure called
directly is refused
([`design/charon-trial/closures`](https://github.com/clicklang/click/blob/master/design/charon-trial/closures/closure.click)).

A `&dyn Fn(i32) -> i32` parameter of scalar parameters and result is a
callback as a `fn` pointer is, and a closure passed for it may capture
variables, `shift(&|y| y + k, x, k)`. The closure's contract names its
captures as its body does, `fn capturing_closures::caller.statement(0).call(0).argument(0)(y:
i32) -> i32 { requires 0 <= k and k <= 1000; ensures result == y + k; }`,
and the callee states what it needs with a parameterized contract,
`requires Adds(f, { amount: k });`. Creating the closure gives a function
value carrying the closure's contract with its captures fixed to the values
captured, and a call requiring another contract of it holds when that
contract refines the required one, the caller's facts about the captured
values included. The refinement uses exact routes and the condition
decider, not search: a capture of `k + 1` whose bound follows from a bound
on `k` is not shown. A shared borrow of a scalar is read when the closure
is created, which safe Rust's freezing of the borrowed variable makes
exact, and a `move` capture is copied. A closure that captures nothing is
its function's address. Captures by mutable reference, `FnMut` and
`FnOnce` callees, and non-scalar captures are refused
([`design/charon-trial/capturing-closures`](https://github.com/clicklang/click/blob/master/design/charon-trial/capturing-closures/closure.click)).

An `impl Fn(i32) -> i32` parameter, or one of a type parameter bound by
`Fn`, `fn apply<F: Fn(i32) -> i32>(f: F, x: i32)`, is a callable value as
`&dyn Fn` is, and the head writes it as the source does; a head has no
`where` clause, so a bound the source writes there goes in the head's
parameter list. A closure passed
for it is checked as one passed for `&dyn Fn`, and a crate function item,
`apply(inc, x)`, is its function's address. The importer reads the
parameter's type from its `Fn` bound and the output type constraint, a
call `TraitClause::call` through it as a call through the value, and the
closure state or `FnDef` constant the caller passes as the value; one
verified body covers every instantiation. Other callable bounds, including
`impl FnMut` and `impl FnOnce`, generic function items, and non-scalar callable
parameters or results are refused; crate trait bounds follow the
method-interface rules below
([`design/charon-trial/impl-fn`](https://github.com/clicklang/click/blob/master/design/charon-trial/impl-fn/closure.click)).

### Trait method interfaces

A method of a crate trait, `pub trait Shape { fn area(&self, scale: i32) ->
i32; }`, has a contract in a `trait` block. Put required methods in an
imported `.interface.click` file and name the trait by its path, as in
`trait trait_methods::Shape { fn area(&self, scale: i32) -> i32 { requires 0
<= scale and scale <= 1000; ensures scale < result and result <= 3001; } }`.
A sidecar verifying a default method declares that method separately in
its own `trait` block.

A call through a trait bound, `shape.area(scale)` for `shape: &T` and
`T: Shape`, or through a `&dyn Shape`, uses that contract. The caller
establishes the `requires` and may use the `ensures`. The head writes a
bound parameter as the source does,
`fn trait_methods::total<T: trait_methods::Shape>(shape: &T, scale: i32)`
or `shape: &dyn trait_methods::Shape`. A call on a known type,
`square.area(scale)`, is a call of that type's implementation, under its
own contract.

Each implementation is written in an `impl` block naming the trait and the
type by their paths, `impl trait_methods::Shape for trait_methods::Square
{ fn area(&self, scale: i32) -> i32 { ... } by { ... } }`, and verified as
any method is. It inherits the interface: the interface's `ensures` join its
own in the `<trait_methods::Circle as trait_methods::Shape>::area.contract`
proof; an implementation that writes no `requires` takes the
interface's. The inherited clauses are read with the implementation's own
names for its parameters: `Square`'s `area` names `scale` as `factor`. It may accept more calls than the
interface, a wider precondition, and its `requires` are checked to follow
from the interface's by the check that forms a named contract at `&f`,
which reads each clause exactly or decides a bare comparison: `requires 0
<= scale; requires scale <= 2000;` follows from `requires 0 <= scale and
scale <= 1000;`. An implementation whose `requires` do not follow is
refused, naming both, as is one with no contract. Without a `trait` block,
a call through the trait has no contract.

A default method, `fn twice(&self, scale: i32) -> i32 { self.area(scale) +
self.area(scale) }` in the trait, can be verified with its contract in a
sidecar `trait` block: `fn twice(&self, scale: i32) ->
i32 { requires ...; ensures result <= 6002; } by { ... }`.
The body is verified once, for every type: a call of `area` in it is a call
through the trait, under `area`'s interface, and with object state it holds
the object as any method of the trait does. A call of `twice` through a
bound or `&dyn` is checked against its interface; a call on a type whose
`impl` keeps the default, `square.twice(scale)`, is a call of the default
body, with the struct packed into its object as for a generic call. An
`impl` that writes its own `twice` inherits and refines the interface as
for any method
([`design/charon-trial/trait-methods`](https://github.com/clicklang/click/blob/master/design/charon-trial/trait-methods/shapes.click)).

The interface's receiver is a reference to a value of a type it does not
know: the interface reads nothing through `self` and holds none of its
resources, except its trait's object state (below), so an implementation whose contract needs the receiver's
fields does not refine it. Every implementation a call can reach is in the
import, since a generic call names its instance's implementation and a
`dyn` coercion its vtable, and each one is checked. The importer refuses a
crate trait with const generics, associated items, or supertraits, a method
that is generic or takes no `&self` or `&mut self`,
parameters other than scalars and type parameters, results other than those or
`Option` of them, an implementation for anything but a
crate struct, and a generic implementation other than one whose type
parameters are its trait's arguments (below)
([`design/charon-trial/trait-methods`](https://github.com/clicklang/click/blob/master/design/charon-trial/trait-methods/shapes.click)).

A crate trait may have type parameters, `trait Scale<T> { fn scale(&self,
x: T) -> T; }`. Each instance the crate implements or calls through,
`Scale<i32>`, is its own interface: its methods are the interface functions
`generic_traits::Scale<i32>::scale`, and its implementations are
`<generic_traits::Square as generic_traits::Scale<i32>>::scale`. A sidecar
may state every instance's interface once, in a block naming the type
parameters, and an instance's in a block naming its types; an instance's
interface is the generic block's clauses with its types for the
parameters, then its own block's. `trait generic_traits::Scale<T> { fn
scale(&self, x: T) -> T { ensures result != x; } }` binds every instance,
and `trait generic_traits::Scale<i32>` adds `requires 0 <= x and x <= 1000;
ensures x < result;` at `i32`. An implementation inherits and refines its
instance's interface in its `.contract` proof, and a call through `S:
generic_traits::Scale<i32>` or `&dyn generic_traits::Scale<i32>` assumes
it. The generic block is also checked once for every type, whether or not
the import uses an instance: its interface, `generic_traits::Scale<T>::scale`,
is lowered with `T` an abstract type, whose values have `==` and `!=` and
nothing else. A clause that needs more, `ensures x < result;`, means
something at some types only and is refused there ("the generic interface
... does not mean something at every type"); it belongs in an instance's
block. A generic block whose object carries state (below) is read so too,
with its object at the abstract types. An instance is taken at `i32`, `u8`,
`u16`, `u32`, `usize` or `bool`, and the importer refuses a default method
of a generic trait
([`design/charon-trial/generic-traits`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-traits/shapes.click)).

Generic code is verified once for every type. An implementation whose type
parameters are its trait's arguments, `impl<T> Keep<T> for Echo`, and a
function generic over a type parameter bound by nothing but `Copy` or
`Clone`, `fn pick<T: Copy>(first: bool, a: T, b: T) -> T`, are imported once
with `T` an abstract type, and the sidecar writes them so, `impl<T>
generic_impls::Keep<T> for generic_impls::Echo { ... }` and `fn
generic_impls::pick<T: Copy>(...)`. A value of `T` is passed, returned,
held in a local and compared with `==` and `!=`; the body is proved once,
and the implementation refines the generic block's interface. A call at
scalar types, `echo.keep(x)` with `x: i32`, calls the instance
`<generic_impls::Echo as generic_impls::Keep<i32>>::keep`, which the import
declares and whose contract is the generic function's at those types: a
clause that reads its abstract values only by `==` and `!=` means the same
at every type. A type parameter is instantiated at `i32`, `u8`, `u16`,
`u32`, `usize` or `bool`, at a crate struct, or at an abstract type of the
calling generic code. At a struct, `exchange<T: Copy>(left: &mut T, right:
&mut T)` called with two `&mut generic_struct_values::Pair` is the instance
`exchange<generic_struct_values::Pair>`, and its `ensures *left ==
old(*right)` compares two struct values: every field of one equal to the
same field of the other. A struct's value is all its fields: `*p`, and a
by-value struct parameter or result compared whole, compare field by field,
and a struct value is written `generic_struct_values::Pair { x: a, y: b }`.
A derived `Clone` of a `Copy` struct, which a `Copy` bound reaches, is the
copy Click already makes
([`design/charon-trial/generic-struct-values`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-struct-values/values.click)).
At an abstract type, `read_twice<U: Copy>` calling `read(cell)` calls `read<U>`, whose
contract is `read`'s with `T` read as `U`, and a call at the callee's own
parameter names calls the generic function itself. A reference to a value
of `T`, `&T` or `&mut T`, points at one value of `T` in memory, its
`sizeof(T)` bytes, as a generic struct's field is: `fn peek<T: Copy>(value: &T) -> T { views
*value; ensures result == *value; }` reads it, and a caller at `u32` lends
`&mut slots.a` as it lends any `&mut u32`
([`design/charon-trial/generic-refs`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-refs/refs.click)).

A generic struct, `struct Cell<T> { value: T, count: u32 }`, holds values of
its type parameters in memory. Each instance a type names is a record of its
own, written with its arguments in the sidecar, `generic_structs::Cell<T>` in
generic code and `generic_structs::Cell<i32>` in a caller. Rust fixes no
layout for a generic struct and safe code reads none, so Click lays each
instance at scalar types out in declaration order, each field at its size
and alignment; the instance at an abstract `T` has a symbolic layout, its
fields at `offsetof` terms and a `T` field taking `sizeof(T)` bytes (below).
A generic function over the
struct, `fn read<T: Copy>(cell: &generic_structs::Cell<T>) -> T { views
cell.value; ensures result == cell.value; }`, is verified once: a store of a
`T` value into a field and a load from it are value moves, and two fields of
`T` are two values. Each instance a call names has the generic function's
signature and clauses at its types, read again at the instance's own layout:
`read<i32>` reads `Cell<i32>`'s `value` at its offset. A sidecar does not
write an instance's block; `fn generic_structs::read<i32>(...)` is refused.
The struct's own methods are written once in a generic `impl` block,
`impl<T: Copy> generic_structs::Cell<T> { fn get(&self) -> T { ... } by
{ ... } }`, named `generic_structs::Cell<T>::get`; a call at `u32` calls
`generic_structs::Cell<u32>::get`, whose contract is the block's at `u32`,
and an `impl` block at an instance, `impl generic_structs::Cell<u32>`, is
refused. A generic struct's field is of one of its type parameters, a
scalar type, or a box or an option of a box of a struct, a generic one's
instance included, laid out at eight bytes; its inherent `impl` blocks name
its parameters in order, and it has no `Drop`
([`design/charon-trial/generic-structs`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-structs/cells.click)).

A generic struct holding a box, `struct Node<T> { value: T, next:
Option<Box<Node<T>>> }`, has drop glue generic over its parameters, verified
once against `impl<T> Destruct for generic_stack::Node<T> { fn
drop_glue(&mut self) { ... } by { ... } }`; a drop at an instance,
`Box<Node<u32>>`'s, calls the glue's instance, `Node<u32>`'s, whose contract
is the block's written out at `u32`. Generic code is instantiated only at the
scalar types, whose values have no drop, so the drop of a value of an
abstract `T` does nothing. A resource over a generic struct is a generic
resource, `resource nodes<T: Copy>(p: *mut generic_stack::Node<T>) { field
values: List<T>; ... }`.
[`design/charon-trial/generic-stack`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-stack/stack.click)
verifies a generic stack, imported unchanged: `Stack<T>`'s `new`, `push`, `pop` and `size` are verified
once for every `T`, `push` and `pop` making the list `Cons(value, old list)`
and its tail and returning `first(old list)`, with `len` the list's length,
and `round_trip` returns `Some(x)` through their instances at `u32`.

A resource takes type parameters as a generic function does, `resource
cell<T: Copy>(c: *mut generic_resources::Cell<T>) { field value: T; owns
c.value; fact c.value == value; }`, and each use names its arguments:
`cell<T>(cell)` in a generic function's contract and proof, `cell<u32>(cell)`
in a caller's. The sidecar writes the resource out at its own parameters,
whose body and the generic functions over it are checked once for every
`T`, and at each argument list a use names, each a resource of its own laid
out at its types; a use in a body is at the instance's arguments. A call to
a generic function consumes and produces the instance at the call's types,
so `fn set_and_get(cell: &mut generic_resources::Cell<u32>, x: u32) -> u32 {
consumes before: cell<u32>(cell); produces after: cell<u32>(cell); ensures
result == x; }`, with the proof omitted, proves through `write<u32>` and
`read<u32>`, holding the produced instance under `after` at the exit
([language reference](language/index.md)). A `step` names a generic callee
with its arguments, `let { after: c } = step(generic_resources::write<u32>(cell,
x), { before: b });`. A generic resource's parameters are abstract types
bound by `Copy` or `Clone` only, and it takes no callable parameters
([`design/charon-trial/generic-resources`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-resources/cells.click)).
A use's type arguments are scalars or crate types named by path, so
`owned_box<boxed::Cell>(b)` is written out at `boxed::Cell`'s layout. A
resource may own a value of an abstract type in its own allocation through
a raw pointer to it: `resource owned_box<T>(p: *mut T) { ...; owns
allocation(p, sizeof(T)); owns *p; }`. There `sizeof(T)` is the number of
bytes a value of `T` takes, a term that is the type argument's own size at
each instance, and `*p` is `p[0u64..sizeof(T)]`
(`charon_generic_resource_owns_a_value_of_any_type_in_its_allocation`). A
generic struct holding a `T`, `Wrap<T>`, has a symbolic layout: rustc may
reorder its fields, so each field lies at `offsetof(Wrap<T>, value)` and the
struct takes `sizeof(Wrap<T>)` bytes, terms that are each instance's own
numbers. Two fields of one object are apart by the layout whatever their
offsets, and each lies inside the object's bytes; a claim that such a size
or offset is one number does not hold for every `T`.

A generic trait's object may carry state, as any trait's does (below). Its
object is a generic resource of the trait's type parameters,
`bags::Bag::object<T>`, whose fields are the generic block's functions:
`function last(self) -> T;` and `function items(self) -> List<T>;`. The
generic block's interface holds the object at `T`, and each instance's at
its types, `bags::Bag::object<i32>`. An `impl` of an instance defines the
functions at its types, `function items(self) -> List<i32> {
List<i32>::Cons(self.value, List<i32>::Nil) }`. The binding uses that instance's
definitions
([`design/charon-trial/generic-trait-objects`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-trait-objects/shapes.click)).

An implementation for every type of a generic struct, `impl<T: Copy>
Holder<T> for Wrap<T>`, is written in the sidecar as the source writes it,
`impl<T: Copy> generic_state::Holder<T> for generic_state::Wrap<T> {
function held(self) -> T { self.value } ... }`, naming the trait's type
parameters as its `trait` block does. Its methods are verified once, with
`T` abstract, on the struct's memory, `<generic_state::Wrap<T> as
generic_state::Holder<T>>::put`, and refine the generic block's interface
read there. Where a caller passes a `&mut Wrap<u32>` as a `Holder<u32>`'s
object, through a bound or `&mut dyn generic_state::Holder<u32>`, it is
packed into `Holder::object<u32>` with the definitions read at `u32`. Its
binding and release use the definitions at the trait instance the import
declares. A struct is packed at an instance's scalar types only
([`design/charon-trial/generic-state`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-state/holders.click)).

### Trait object state

A trait block may declare model functions of its object, `function
size(self) -> i32;`, which are the object's state: the trait's object is a
sealed abstract resource, `trait_objects::Shape::object`, with a field for
each function. A `&self` or `&mut self` method of the trait, a parameter
`x: &T` or `x: &mut T` with a `T: Trait` bound, and `x: &dyn Trait` or
`x: &mut dyn Trait` each hold the object `x` refers to, with no clause
written for it, and read its state as `size(x)`. A shared reference keeps
it, so the caller still knows `size(x)` after the call, and an `ensures`
reads it as it was at entry. A mutable one may change it: an `ensures`
reads the new state, `size(self) == half + half`, and `old(size(self))` the
state at entry, and the caller knows only what the `ensures` say. No proof
folds or unfolds the object: it has no body. A trait's model declarations
and required method contracts can live in an imported `.interface.click`
file. The sidecar's
`impl` blocks define the model functions and verify the methods against
those contracts.

The same field can be written `object_resource(x).size`. This selects
the resource already associated with the receiver `x` in the contract.
Checked certificates can use that form for field reads.

Each `impl` of such a trait defines every function from its type's
fields, `function size(self) -> i32 { self.side }`; an `impl` that omits
one is refused. Its methods are stated on the struct's own memory, `owns
*self` for `&self` and `&mut self`, with `size(self)` read as the definition in its own
clauses and in the interface's it inherits, and its proof is an ordinary
method proof. Click checks refinement against the inherited interface on
that memory, using the implementation method's identity.

Where a struct reference becomes the object, at a call that instantiates a
bound type parameter with the struct or coerces it to `&dyn Trait`, the
importer binds the object before the call and releases it afterward. Click
selects the transfer contract by concrete type, trait instance, and borrow kind.
Proofs can
select the binding by its written call and argument, for example
`statement(1).call(0).argument(0).binding`. A method call uses
`.receiver.binding` for the receiver. The suffix `.release` selects the matching
transfer back after the call. At the binding frontier,
`let { object_resource(): packed } = step(statement(1).call(0).argument(0).binding);`
names the resource so the proof can read `packed.size`. For a `&mut`
reference, pack consumes the struct's memory and produces its object, whose
fields are the definitions read on it, and unpack returns the memory with
the definitions equal to the fields. For a shared reference, the shared pack
views the memory and produces, beside the object, a resource that keeps the
memory lent until the shared unpack consumes both; nothing can change it
meanwhile, so the caller keeps every field. An implementation's `&self`
method likewise only views `*self`. A caller passing `&Square { side: 3 }`
therefore knows `size` is `3` and gets the interface's guarantee read with
that value, and keeps the fields `size` does not read (`tag_after_dyn`); one
lending `&mut square` gets back a struct whose fields the definitions equate
to the object's new state, so after `reset(&mut square, half)` it knows
`square.side == half + half` and nothing of the side it lent. A default
method's body holds the object as the trait's other methods do. A generic
trait's object is a generic resource (above)
([`design/charon-trial/trait-objects`](https://github.com/clicklang/click/blob/master/design/charon-trial/trait-objects/shapes.click)).

An implementation whose object's state is not in its struct's fields, such
as a value in a box the struct points at, names the resource holding it in
its `impl` block, `resource state: boxed(self.item);`, and defines the
trait's functions from that resource's fields, `function item(self) ->
Option<u32> { state.value }`. Its methods hold the resource beside the
struct's memory, `owns state: boxed(self.item)`, with arguments read where
the clause is, so a method that replaces the box leaves `state` at the new
`self.item`. The pack consumes the resource with the memory, and the unpack
produces a new instance holding the object's final state. A caller that
lent its own, `owns state: boxed(slot.item)`, holds that instance under
`state` at its exit
([`design/charon-trial/resource-state`](https://github.com/clicklang/click/blob/master/design/charon-trial/resource-state/slots.click)).

The resource may be generic, and the functions any type its fields have. The
generic stack implements `trait Container<T>` once for every `T` with
`resource state: nodes<T>(self.head); function items(self) -> List<T> {
state.values }`, beside `function size(self) -> usize { self.len }`. The
interface's clauses may compare mathematical integers of the object's
state, `requires to_integer(size(self)) == length(items(self));`, and the
refinement check reads them on the implementation's memory and resource
as it reads other clauses; an `Integer` range fold in such a clause is
refused. A function's proof names a parameter's object
state as its clauses do, `apply(first_cons(x, old(items(container))));`, so
a caller through `&mut dyn Container<u32>` can apply lemmas about the list
([`design/charon-trial/generic-container`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-container/container.click)).

### `extern` block functions

A `safe fn` declared in an `unsafe extern "C" { ... }` block has no body in
the crate, and a call to it needs no `unsafe`. The sidecar imports `ffi.interface.click`, which states the contract for
`fn extern_functions::clamp_reading(raw: i32) -> i32`. A caller must establish
the `requires` and may use the `ensures`. An interface contract takes no
program proof. A verified `fn` for such a declaration is refused. Charon keeps no parameter names for a foreign item, so the head
names them; its types must be the declaration's. Parameters and the result
are scalars, or `()` for the result. An `unsafe fn` item and other ABIs are
refused, as their calls need `unsafe`. Functions of other crates are not
imported
([`design/charon-trial/extern-functions`](https://github.com/clicklang/click/blob/master/design/charon-trial/extern-functions/ffi.click)).

### Core library methods

A call of a Rust core integer method, `a.min(b)`, `x.checked_add(y)` or
`n.unsigned_abs()`, calls an external function whose contract is a one-line
contract in `library/rust/integers.interface.click`
([Rust integer methods](library/index.md#rust-integer-methods)):
`extern fn u32::min(a: u32, b: u32) -> u32 { ensures result ==
click::rust::u32::min(a, b); }`. The importer appends the line of each method
an import calls, and only those. The extern's path names the program's
function; its `ensures` names the specification function of the same path,
which the library defines, with the others of each integer type, in
`library/rust/<type>.click`
([Rust core methods](library/index.md#rust-core-methods)), so
a sidecar writes the same function after importing its module: after
`import click::rust::u32;`, `fn smaller(a: u32, b: u32) -> u32` calling
`a.min(b)` verifies `ensures result == u32::min(a, b);`.

The importer recognizes `min` and `max` of `Ord` and the inherent
`wrapping_add`, `wrapping_sub`, `wrapping_mul`, `saturating_add`,
`saturating_sub`, `checked_add`, `checked_sub` and `abs_diff` of every
integer type, and `unsigned_abs` of a signed one, by the callee's identity and
signature. A `checked_*` result is the library's `Option`. `o.unwrap_or(d)` of
an `Option` of a scalar calls `Option::unwrap_or` the same way, whose contract
states its result with `click::rust::option::unwrap_or(o, d)`. A
sidecar can selectively import the helper with
`import click::rust::option::{unwrap_or};`. The `Result` method uses
`click::rust::result::unwrap_or` ([Result values](#result-values)). `unwrap` and `expect` are described under
[Panics](#panics). The library
function is opaque until `unfold` gives its definition, so a claim that needs
the value, `result <= a`, unfolds it, and a proof of one arm states the value
there: `have u32::min(a, b) == a by { unfold(u32::min(a, b)); close(); }`.
Each contract is an assumption, listed in [trust](../concepts/trust.md); each
library function is checked at the edge of its type in
`mdtests/stdlib_every_symbol.md`.
[`design/charon-trial/core-methods`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.click)
verifies calls at several widths.

`xs.swap(a, b)` on a mutable slice of integers calls an instance of
`slice::swap<T>`, whose contract states the call's effect rather than a
result. The contract is the generic `extern fn` block in
`library/rust/core.interface.click`, written out at each called element type as a
sidecar's generic function is, with the instance's own parameter names by
position. The other non-integer core methods are stated there the same way:
the `Vec` methods ([Vec values](#vec-values)), `Option` and `Result`
`unwrap`, `expect` and `unwrap_or` ([Panics](#panics),
[Result values](#result-values)), and the slice-iterator operations
([Rust core interfaces](library/index.md#rust-core-interfaces)). The importer
writes no contract text; it keeps only a name table from each core method to
its library file. The instance at `u32` is:

```text
extern fn slice::swap<u32>(s: &mut [u32], a: usize, b: usize) {
    owns *s;
    requires a < s.len();
    requires b < s.len();
    ensures s[a] == old(s[b]);
    ensures s[b] == old(s[a]);
    ensures forall (k: usize) { k < s.len() and k != a and k != b implies s[k] == old(s[k]) };
}
```

The two `requires` are Rust's index panics, so a caller shows both indices in
bounds. An element the call keeps is the last clause at its index: after the
call, `instantiate(forall (k: usize) { ... }, 1u64)` gives `xs[1] ==
old(xs[1])` once `1u64 < xs.len()` is held. Other core methods, such as `pow`,
remain unmodeled calls, refused with the callee's name.

## Supported semantics

The scalar slice supports every integer width but 128 bits, `i8`, `i16`,
`i32`, `i64`, `isize`, `u8`, `u16`, `u32`, `u64` and `usize`, each the C
integer of its width, `isize` and `usize` the target's 64 bits; booleans,
unit returns, initialized scalar
and reference locals, branches, direct calls within the selected file,
references to integers, and plain structs with integer or reference fields,
enum fields of any integer width or `bool`, and `Option` of any of them, field
access, local reborrowing of reference-backed places, and borrows of integer,
`bool`, enum and type-parameter locals ([Option values](#option-values)).
Arithmetic supports addition, subtraction, multiplication, division and
remainder at every width; negation at the signed widths; bitwise operations at
every width but `i8` and `i16`; shifts at every width; comparisons;
and boolean operations. Signed division and remainder truncate toward zero, as
in C. Each operation that could overflow owes Rust's panic check: an explicit
range check, labeled `Rust add panic check`, at the 8- and 16-bit widths, whose
arithmetic is computed in `int`, and at the unsigned 32- and 64-bit widths, and
the kernel's signed-overflow check at `i32`, `i64` and `isize`. Division and
remainder owe a nonzero divisor, and at the signed widths not `MIN / -1` or
`MIN % -1`: the kernel's check at `i32`, `i64` and `isize`, and `Rust div
panic check` or `Rust rem panic check` at `i8` and `i16`, where `MIN / -1`
fits `int`. Negation `-x` lowers as `0 - x` and owes the subtraction's check.
A shift owes `Rust shl panic check` or `Rust shr panic check`, that its count
is below the operand's width (a negative count is out of range too). A signed
left shift wraps, as Rust's does: the bits are shifted as an unsigned word and
reinterpreted at the operand's width. A signed right shift is arithmetic. An
exact claim such as `result == (x << n)` proves at `i32`, and `result == (x >>
n)` at `i32` and `i64`; at `i8`, `i16` and a 64-bit left shift the
reinterpreted result is not yet related to the spec's shift.
At `u8` and `u16`, remainder uses the same signed 32-bit promotion as its
contract expression; both operands fit that range and remain nonnegative.
A precondition such as `x % 2u8 == 0u8` therefore proves the corresponding
branch or `assert!` guard without an explicit proof. The nonzero-divisor
obligation still applies
([`design/charon-trial/narrow-remainder`](https://github.com/clicklang/click/blob/master/design/charon-trial/narrow-remainder/widths.click)).
For `i8` and `i16`, the nonzero divisor and narrow overflow exclusion
also establish that the promoted result fits the original type. Contracts
can use the normal Rust domain for either sign of the operands
([`design/charon-trial/signed-arithmetic`](https://github.com/clicklang/click/blob/master/design/charon-trial/signed-arithmetic/signed.click)).
A core `From` between
integers converts when every source value is a target value. Integer `as`
casts preserve Rust truncation and bit interpretation
([`design/charon-trial/integer-widths`](https://github.com/clicklang/click/blob/master/design/charon-trial/integer-widths/widths.click)).
A struct owned whole, `owns *account`, is held at its fields' widths, so
a 64-bit field reads as one value, as `deposit` there does. Record
size, alignment, and field offsets come from rustc for the selected target;
Rust's default field order is not assumed.

Single-file units use Rust 2024; crate units select
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
uses ordinary Click contracts and tactics. Expansion uses ordinary Integer laws and explicit normalization for widened
word bounds.
The [unchanged Adler2 computation](https://github.com/clicklang/click/blob/master/design/adler32/project/adler2/README.md)
is verified separately against the common checksum specification for every
slice length from canonical initial states. The unchanged `write_slice` and
`adler32_slice` wrappers compose checked bodies for every length, preserve
input bytes, and prove field and packed checksum correctness. A locked client
also proves that two actual updates equal the full-input checksum for every
valid split. The unchanged `from_checksum`
constructor is checked for every `u32` checksum. A separate
[resumed client](https://github.com/clicklang/click/blob/master/design/adler32/project/adler2/resumed.click)
restores the checksum of a checked prefix, updates with the suffix, and proves
the full-input checksum and byte preservation for every length and valid
split. Arbitrary saved words need not satisfy the canonical-seed preconditions
for an update.

```console
cargo run --bin click -- import lock examples/rust-unsigned/arithmetic.click
cargo run --bin click -- verify examples/rust-unsigned/arithmetic.click
```

## Panics

A Rust panic is an obligation: Click proves no call reaches it. A block that
can only reach a call of `core::panicking`, the target of `assert!`,
`assert_eq!`, `assert_ne!`, `panic!`, `unreachable!`, `todo!` and
`unimplemented!`, is one obligation
named by the panic's message, ``Rust panic `assertion failed: x > 3` ``; the
statements that build the message, `format_args!` included, are not modeled,
because a block shown unreachable has no effect. A branch whose one side
panics is the assertion of the other side's condition, so after
`assert!(x > 3)` the fact `x > 3` holds, and a refusal names the condition as
its goal, ``could not show `x > 3u32` ``. A message with formatted arguments is
named `formatted message`. `o.unwrap()` and `o.expect("...")` of an `Option` of
a scalar call `Option::unwrap<T>` and `Option::expect<T>`, whose contract
requires `o != Option<T>::None` and ensures `o == Option<T>::Some(result)`;
`expect`'s message is not passed. `Result`'s `unwrap` and `expect` are
described under [Result values](#result-values). `assert_eq!(a, b)` asserts `a == b` and
`assert_ne!(a, b)` asserts `a != b` of scalar operands, named ``Rust panic
`assertion left == right failed` `` or `left != right` whatever their own
message; the pair of borrows the macro compares through, `(&a, &b)`, reads
the operands themselves
([`design/charon-trial/panics`](https://github.com/clicklang/click/blob/master/design/charon-trial/panics/panics.click)).

## Byte slices and indexing

Shared `&[u8]` and mutable `&mut [u8]` parameters, local copies and reborrows,
builtin `.len()`, indexed reads and writes, and direct slice calls are supported.
A slice reference is one value, its data pointer and its length, as Rust
passes it. A shared slice has a shared data pointer and a mutable slice has a
mutable one. Proofs use `bytes.len()`
for a slice parameter or local named `bytes`. After a local is reassigned,
`at(point, bytes.len())` reads the length it held at the selected point.
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
limit on the length. `.len()` alone needs no byte resource. A function returns a slice as one
value, its data pointer and length. Range subscripts, indexed compound assignment, and
other slice element types remain unsupported. Supported shared slice splitting
is described below. Numeric contract casts are `x as i32`, `x as u32`,
`x as i64`, `x as u64` and the other scalar types, and like Rust `as` they
convert modulo 2^N. Use signed 64-bit widening to state full-width u32
addition guards, for example `(x as i64 + y as i64) <= 4294967295i64`.

## String slices

A `&str` parameter is a shared slice of the UTF-8 bytes it refers to: one
string slice value of type `Str`, its data pointer and its length in bytes.
A pure function's `&str` parameter takes it as that value. A sidecar
writes its type `&str` and reads its length as `s.len()`; the type grants
the same authority a `&[u8]` does. A reborrow `&*s` and a call passing a
`&str` on are supported. `s.len()` and `s.is_empty()` call `str::len` and
`str::is_empty`, one-line contracts in `library/rust/str.interface.click`
([Rust string slice methods](library/index.md#rust-string-slice-methods)),
reported as assumptions:

<!-- verified-example: tests/fixtures/rust-verification/str-views/strs.click -->
```click
verifying "strs.rs";

// A `&str` is a shared slice of its UTF-8 bytes: a contract reads its
// length in bytes as `s.len()`, as the code does. The library states
// `str::len` and `str::is_empty` over that length.
fn str_views::byte_len(s: &str) -> usize {
    ensures result == s.len();
}

fn str_views::blank(s: &str) -> bool {
    ensures result == (s.len() == 0u64);
}

// A call passes the string slice on, and the callee's contract gives its
// length.
fn str_views::longer(a: &str, b: &str) -> bool {
    ensures result == (a.len() > b.len());
}

// `is_empty` decides the branch, so each case gives its own result.
fn str_views::width(s: &str) -> usize {
    ensures s.len() == 0u64 implies result == 1u64;
    ensures s.len() != 0u64 implies result == s.len();
}
```

A `&str` in a value position, a pure function's parameter or result or a
theorem binder, is one string slice value of the type `Str`
([`click::rust::str`](library/index.md#clickruststr)): the same data pointer
and byte length as a byte slice, at its own type. Its methods are `str`'s:
`s.len()`, `s.as_ptr()` and `s.as_bytes()`, the same bytes as a `&[u8]`, all
read in place with no `unfold`. `click::rust::str::from_utf8_unchecked(v)`
makes a string slice of a byte slice `v`. A string slice is no byte slice:
`s[i]`, `s[a..b]`, a `&[T]` parameter and `s == bytes` refuse it, naming its
type. Failures print a string slice in these spellings.

A function may return a `&str`, as one string slice, and its contract reads
`result.len()` and `result.as_ptr()`. In imported Rust code, `s.as_bytes()`
calls `str::as_bytes`, whose one-line contract gives the same data pointer
and length as a `&[u8]`, reported as an assumption. The code reads the
result with the byte slice's methods, so its length is the string's and an
index into it is checked against that length:

<!-- verified-example: tests/fixtures/rust-verification/str-bytes/bytes.click -->
```click
verifying "bytes.rs";

// `s.as_bytes()` calls the library's `str::as_bytes`, whose contract gives
// the string's bytes as a byte slice: the same data pointer and length.
fn str_bytes::byte_count(s: &str) -> usize {
    ensures result == s.len();
}

// The byte view has the string's length, so its first byte is in bounds
// whenever the string is not empty, and it is the string's first byte.
fn str_bytes::first_byte(s: &str) -> u8 {
    requires 0u64 < s.len();
    views *s;
    ensures result == click::rust::str::as_bytes(s)[0];
}
```

The result must be bound to a local first: `s.as_bytes().len()` is refused as
an unnamed compiler local, as any call's slice result read in place is. An
index into the bound local that may be out of bounds is refused with its
condition over the local, `0u64 < bytes.len()`. A
byte read through the result is the string's byte, so
`ensures result == click::rust::str::as_bytes(s)[0];` is proved. A
contract spells the byte view of a `fn`'s `&str` parameter that way: the
parameter's methods there are `s.len()` and `s.as_ptr()`. `&mut str`,
`String`, string literals, `==` and the other `str` methods are refused with
their names. The UTF-8 validity of a `&str`'s bytes is not modeled.

## Shared slice splitting

The standard shared byte-slice method supports local destructuring:
`let (left, right) = bytes.split_at(mid)`. The exporter checks the resolved
core slice method and retains a `SliceSplit` operation. The receiver must be
a local `&[u8]`; both tuple elements must be plain bindings. General tuple
values, wildcard patterns, direct array receivers, mutable slice receivers,
and `split_at_mut` remain unsupported.

The receiver's pointer and length are captured before evaluating the midpoint,
which is evaluated once. Execution checks `mid <= bytes.len()` at the full
64-bit `usize` width. The left slice keeps the original pointer and length
`mid`; the right starts at `bytes.as_ptr() + mid` and has length `bytes.len() - mid`.
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
starts also restore backing for array-field state copies. The loop contract
need not list compiler-created local arrays as input resources. Re-entry checks
live borrows and replaces the previous object's identity; initialization and
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

```console
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

A shared or mutable slice of any integer element, `&[i64]` or `&mut [u16]`,
is a pointer and a length, as a byte slice is: indexed reads and writes owe
`Rust slice index panic check`, `xs.len()` is the length, a slice passes to a
callee whole, a guard may read either kind's length, and a shared slice
iterates by the remaining count `for &x in xs` keeps
([`design/charon-trial/scalar-slices`](https://github.com/clicklang/click/blob/master/design/charon-trial/scalar-slices/slices.click)).
Slices of records or of slices, by-value array parameters or returns, and
nested arrays remain unsupported. Supported flat records can contain owned array fields,
including in crate-unit record returns described above. Imported
assignment-operator bodies support indexed `u32` updates, as checked by the
[assignment-operator fixture](https://github.com/clicklang/click/blob/master/design/charon-trial/assignment-operators/operators.rs).
The builtin length operation also supports non-byte fixed arrays by
recovering their fixed length; this does not enable general library
methods.

Single-file units exclude modules and imports; crate units support
the locked module closure described above. Macros, semantic attributes,
dependencies, unsafe code, heap allocation beyond
[boxes](#boxes), nested aggregate parameters,
reference returns other than slices, and other integer widths are outside this slice. Trait
dispatch and type parameters are limited to the forms described under
[callable bounds](#function-pointers-and-named-contracts) and
[trait method interfaces](#trait-method-interfaces); const generics
remain unsupported. Unsupported syntax
fails during extraction or direct lowering. This is not general Cargo-project
support.

## While loops and invariants

`while` loops, including nested and labeled loops, use the shared checked
loop rules. Sidecars can declare `invariant`, memory/resource clauses, and numeric
`decreases` measures. Entry and preservation are separate obligations;
arithmetic and indexing in the body retain Rust's panic-freedom checks.
A decreasing measure proves termination through the existing loop checker.
Charon locals with unique source names use those names in sidecars. A
compiler temporary that holds part of a source expression is put back into
that expression, and a call nested in an expression, as in
`or_zero(ok_if(x, true))`, is a call step whose result a proof names by its
call, `call(result_values::ok_if, 0).result`
(`charon_a_nested_call_result_is_named_by_its_call`). A proof names a
point by the statements as written, `statement(i)`, `S.statement(j)`,
`S.call(f, j)` and the rest, as a C proof does; Click reads them from the
source with `syn` (`src/languages/rust/source_statements.rs`). A source name
bound more than once, as `word` in two `Some(word)` arms, `x` in two `match`
arms, or a shadowing `let`, is one declaration per binding, as in C: each
starts where rustc starts its storage and ends where rustc ends it, so a
proof's `word` names the live one. Inside `let x = x + 1;` the new `x` has the
name from its storage start, before its value is written, as a C declarator's
scope starts before its initializer. `f.statement(3).local(word)` names the
`word` that statement declares, and `f.local(i)` names a declaration by its
position among the function's locals; diagnostics write a repeated name in
that canonical form, `"lib.rs"::f.local(5)`
(`charon_repeated_source_names_are_distinct_declarations`). The importer
can retain an unnamed operand as an expression value, including some
arithmetic operands and enum call results. When the importer still lowers
an unnamed MIR local as a binding, its compiler identity can change when
the artifact is refreshed.

A materialized array or struct literal, such as the array in `read(&[x, 7])`,
can be named as `f.compound_literal(i)`. The index counts written array
and struct literals in the function from zero, including repeat expressions
such as `[x; 2]`. For example, read the array's first element as
`f.compound_literal(0)[0]` or a struct's field as `f.compound_literal(0).value`.
Use a program point where the object's storage is live. A recorded point can
still name the object that was live there.

Conditions currently support scalar comparisons, boolean combinations,
negation, casts, and builtin `.len()`. Calls, indexing, and arithmetic in a
condition require repeated preparation of checked operands and are rejected.
`loop`, `break` (with or without a value) and `continue` are supported.
A loop whose body breaks lowers to `while (1)` whose test also exits by
`break`, so each exit runs its own path, including its storage ends, to the
code after the loop
([`design/charon-trial/loop-control`](https://github.com/clicklang/click/blob/master/design/charon-trial/loop-control/control.click)).
Every exit of a loop reaches one join through straight blocks, or returns.
A `return` from a loop body, from any depth, runs straight to the function's
exit as a C `return` does, so the loop's invariants are not owed on that path
and the contract is checked there. A labeled `break 'outer` or `continue
'outer` from an inner loop leaves each loop it crosses: the inner loop exits
and the enclosing loop takes the corresponding `break` or `continue` path.
Click keeps the routing state private. In a written `maintain`, a body branch that returns is a proof-level `if` whose
returning arm steps to
`function.exit`
([`design/charon-trial/early-exits`](https://github.com/clicklang/click/blob/master/design/charon-trial/early-exits/exits.click)).
General iterators remain unsupported; the slice, array, range and `enumerate`
`for` forms described below are supported.

[`examples/rust-loops/loops.rs`](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.rs)
and its [sidecar](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.click)
verify a scalar counter, checked accumulation, and a byte-slice walk with a
full-width `usize` counter. The walk uses `invariant i <= bytes.len()` and
`decreases bytes.len() - i`; slice access requires `views` authority.
Full-width range endpoints retain the target’s `usize` width; contracts using
signed indices must separately justify their conversions. The accumulator contract fixes the added value
to one. These are synthetic loop regressions, not a checksum-library proof.
Verification, profiling, auditing, and proof expansion use the shared engine.

```console
cargo run --bin click -- import lock examples/rust-loops/loops.click
cargo run --bin click -- verify examples/rust-loops/loops.click
```

The [byte-sum example](https://github.com/clicklang/click/blob/master/examples/rust-byte-sum/sum.click)
proves a functional loop over arbitrary input bytes. For slices of length
`0..=1000`, its unchanged Rust source returns the exact mathematical sum of
the input at function entry. A prefix fold
and the bound `0 <= total and total <= 255 * i` establish the result and
safety of every intermediate addition. It covers empty input and supports
profiling, audit, and expanded-proof reverification.

A loop's clauses read its pass count as `iterations`, and a Rust local of
that name as `program::iterations`: `program::name` names a program binding a
Click name shadows, in Rust as in C
([`design/charon-trial/program-bindings`](https://github.com/clicklang/click/blob/master/design/charon-trial/program-bindings/bindings.click)).

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
branches. An iterator is held as the slice it still covers, the slice
`iter.as_slice()` returns: one slice value, with its data pointer and its
length. `core`'s `slice::Iter`
holds the same slice as a start and an end pointer. Each successful
`next()` yields the element at `iter.as_slice().as_ptr()`, binds the loop variable to
its shared address, and moves the slice on by one element before entering
the Rust body; no `Option` or compiler temporary holds it, as for a range. A
`match` on `next()` whose `Some(_)` arm binds nothing only moves the slice
on. An exhausted iterator exits without a read, including for an empty
slice.

A proof reads a loop's iterator as `iter` inside that loop's clauses and
phases, and as `loop(i).iter` anywhere, through Rust's own methods:
`iter.len()` is the length left, and `iter.as_slice()` the remaining
elements, a slice that reads as a slice parameter does: `iter.as_slice()[k]`,
`iter.as_slice().len()` (which is `iter.len()`) and its data pointer
`iter.as_slice().as_ptr()`. Pointer comparisons and arithmetic are written on
`iter.as_slice().as_ptr()`, as on a slice parameter's `bytes.as_ptr()`; a
slice compared with a pointer, `iter.as_slice() == bytes.as_ptr()`, is a type
error naming `.as_ptr()`. The importer records which iterator each loop
advances, so the iterator needs no name of its own; diagnostics print its
state the same way. Where the iterator stands is an invariant the proof
states:

```text
loop {
    decreases iter.len();
    views bytes[0..bytes.len()];
    invariant iter.len() <= bytes.len();
    invariant iter.as_slice().as_ptr() == bytes.as_ptr() + (bytes.len() - iter.len());
    ...
}
```

Moving the slice on from `bytes.as_ptr() + k` to `bytes.as_ptr() + k + 1` owes the offset's
bound in the forms the step reads, `to_integer(k) + 1 <=
to_integer(bytes.len())` and `to_integer(k + 1u64) <= to_integer(bytes.len())`,
and the invariant is carried by regrouping `(bytes.as_ptr() + k) + 1u64` as
`bytes.as_ptr() + (k + 1u64)` from `to_integer(k) + 1 <= 18446744073709551615`
([full-width pointer association](tactics/index.md#simplification-with-selected-premises)).
A `maintain` script splits on `0u64 < iter.len()` with a proof `if`; the
empty arm steps to the exit
([`examples/rust-iterators/sum.click`](https://github.com/clicklang/click/blob/master/examples/rust-iterators/sum.click)).

There is no generated processed-count or index variable. Sidecars choose their
own properties of iterator state. The sum examples derive a processed prefix
as original length minus remaining length; the remaining length also proves
termination. This length is the iterator's remaining slice metadata,
represented as full-width `uint64` for the locked 64-bit target. Signed
prefix-index observations require a checked range and conversion in the
sidecar. Reads require view authority and body arithmetic retains its panic
checks. Immutable slice bindings keep the original pointer and length stable;
mutable bindings and slices are rejected.

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
[array iteration example](https://github.com/clicklang/click/tree/master/design/charon-trial/array-iteration).
The compiler retires an iterator's source when it is moved; repeated
exhaustion yields no element.

`for (i, x) in xs.iter().enumerate()` over a slice of any integer width is
`core`'s `Enumerate { iter, count }`: the slice iterator above and `count`,
how many elements it has yielded, which a proof reads as `iter.count`
(`iter.len()`, `iter.as_slice()` and `iter.as_slice().as_ptr()` read the slice iterator). The exporter
checks that `enumerate` is the core `Iterator::enumerate` default method and
that `next` is the core `impl<I: Iterator> Iterator for Enumerate<I>`. Each
iteration yields index `iter.count` and the element at `iter.as_slice().as_ptr()`,
then counts it and moves the slice on; a reference pattern `(i, x)` binds
the element's address and a copied pattern `(i, &x)` reads it.
[`design/charon-trial/enumerate`](https://github.com/clicklang/click/blob/master/design/charon-trial/enumerate/enumerate.click)
proves the last index a loop yields with `iter.count == xs.len() - iter.len()`
and `iter.as_slice().as_ptr() == xs.as_ptr() + iter.count`.
`.iter_mut()` and by-value array iteration remain outside this subset; a
crate's own iterator is [below](#crate-iterators).

## Range loops

`for i in a..b` over an integer `a..b` of any admitted width holds the range
as its two bounds, of its element type. A proof reads them through the
range's own public fields, `iter.start` and `iter.end`, inside the loop, and
`loop(i).iter.start` anywhere; `iter.len()` is `iter.end - iter.start`. In
nested loops `iter` is the inner loop's iterator inside it, and the outer
one is `loop(i).iter` there. A range stored in a local first,
`let r = a..b; for i in r`, is the same. The exporter checks that
`into_iter` and `next` are the core
`impl<I: Iterator> IntoIterator for I` and `impl<A: Step> Iterator for
Range<A>`. `next` yields `Some(iter.start)` and advances `iter.start` while
`iter.start < iter.end`, else `None`; the advance owes the addition's check,
which the guard decides. The loop's variable is bound where `next` yields:
`i = iter.start`, then the advance. The `Option` is never built, and no
compiler temporary holds it.

Invariants are written over the bounds: `decreases iter.end - iter.start`
ranks the loop, and after it the exit guard gives `iter.start >= iter.end`.
[`design/charon-trial/ranges`](https://github.com/clicklang/click/blob/master/design/charon-trial/ranges/ranges.click)
verifies counts over `u32`, `i32` `a..b` and `i64` ranges, the last byte a
loop over `0..bytes.len()` reads, and nested ranges.

For an inclusive range `a..=b`, proofs use `iter.is_empty()` to tell
whether there is another item, and `iter.start()` and `iter.end()` to
read the bounds while the range is nonempty. A reversed range starts
empty. A nonempty range becomes empty after yielding its endpoint, even
when that endpoint is the largest value of the integer type.

The counting proofs in
[`design/charon-trial/inclusive-ranges`](https://github.com/clicklang/click/blob/master/design/charon-trial/inclusive-ranges/inclusive.click)
rank the loop by the original length minus the number counted. While the
range is nonempty, its start is the next value to count. Once it is
empty, the count equals the original length. This also covers
`0u8..=255`, whose count is 256. `.rev()`, `.step_by()` and other range
adapters remain later work.

## Primitive unsigned conversions

Calls such as `u32::from(byte)` and `<u32 as From<u16>>::from(half)` support
compiler-resolved core `From` conversions between modeled unsigned scalar
types (`u8`, `u16`, `u32`, `usize`) when the source width is no greater than
the destination width. The Charon adapter validates the selected core
implementation, signature, and concrete types before constructing Click's
`IntegerFrom` operation;
lowering preserves the value and evaluates its argument once in source order.
These pinned standard-library primitive conversions are interpreted builtins;
their library bodies are not imported. Matching a method's name alone does
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
compiler's standard iterator/Option desugaring. `chunks.remainder()` checks
the resolved core inherent method and retains a `ChunkRemainder` expression.
The receiver is a shared byte-slice local; parameters or returns of iterator
type, adapters, and explicit `next()` calls are unsupported. Mutable chunk
iterators and chunks of non-byte slices remain unsupported.

An iterator is held as its own fields, the ones `core::slice::ChunksExact`
declares: `v`, the chunks still to come, `rem`, the elements they leave
over, and `chunk_size`. A slice field is its data and its length. The
importer runs `core`'s own code over them:

- `bytes.chunks_exact(size)` panics on a zero size (the `Rust chunks_exact
  panic check`), then sets `chunk_size = size`, `v` to the first
  `bytes.len() - bytes.len() % size` bytes, and `rem` to the rest;
- `next()` yields `None` while `v.len() < chunk_size`; otherwise it yields
  `v`'s first `chunk_size` bytes and moves `v` on by `chunk_size`;
- `remainder()` returns `rem`.

Construction evaluates the size once. Input lengths and chunk sizes keep the
locked target's `usize` width. The compiler enforces moves and borrows.
Neither `next()` nor `remainder()` copies bytes or creates write authority:
reads through chunks, aliases, calls, and tails need the original input's
views, and so does moving `v` on, whose result must stay inside the input.
No trusted chunk contract is involved.

In a loop's clauses and phases a proof reads the iterator the loop advances
through its fields: `iter.v`, `iter.v.len()`, `iter.rem`, `iter.rem.len()`
and `iter.chunk_size`, and `iter.len()` is `iter.v.len() / iter.chunk_size`,
Rust's `ExactSizeIterator::len`. `loop(i).iter` names them outside the loop.
Inside a loop, `iter` is the loop's iterator even where the function has a
local of that name. A pass's `next()` splits on `iter.chunk_size <=
iter.v.len()`, so a `maintain` script splits the same way with a proof `if`;
the other arm takes the exit with three `step()`s. A chunk is still `chunk`
and `chunk_len`, and the remainder `tail` and `tail_len`.

Where the iterator stands is an invariant over `v`:

```text
loop {
    decreases iter.v.len();
    views bytes[0..bytes.len()];
    invariant iter.chunk_size == 4u64;
    invariant iter.v.len() <= bytes.len() - bytes.len() % 4u64;
    invariant iter.v == bytes.as_ptr() + (bytes.len() - bytes.len() % 4u64 - iter.v.len());
    ...
}
```

A pass moves `v` from `bytes.as_ptr() + k` to `bytes.as_ptr() + k + 4`. The proof states the
offset's bounds in the forms the step owes, `to_integer(k) + 4 <=
to_integer(bytes.len())` and `to_integer(k + 4u64) <= to_integer(bytes.len())`,
and regroups `(bytes.as_ptr() + k) + 4u64` as `bytes.as_ptr() + (k + 4u64)` from
`to_integer(k) + 4 <= 18446744073709551615`
([full-width pointer association](tactics/index.md#simplification-with-selected-premises),
[proof](https://github.com/clicklang/click/blob/master/examples/rust-chunks-exact/chunks.click)).
A read through the chunk, `chunk[3]`, is a read of `bytes` at `k + 3`.

## Crate iterators

A `for` loop over a value of a crate struct with its own `impl Iterator`
calls that `next` each pass, as written. The struct is the loop's
iterator, so a proof reads its fields as `iter.<field>` inside the loop and
`loop(i).iter.<field>` anywhere. `next` is an ordinary crate function under
its own contract, declared in the sidecar's `impl Iterator for S` block and
proved from its body. The exporter checks that `into_iter` is the core
`impl<I: Iterator> IntoIterator for I`, which moves the struct into the
loop's iterator, and that `next` is the crate's local, non-generic
`Iterator::next` for that struct.

The `Option` that `next` returns is no local. The loop tests the call's
result for `Some` without ending it, and the `Some` arm's payload read binds
the loop variable and ends it. A pass is decided by `next`'s contract. When
the contract's cases are stated over the iterator's fields, a `maintain`
script splits on the same fields with a proof `if` and states the case's
premise in the contract's own form before the call:

```text
fn count(n: u32) -> u32 {
    ensures result == n;
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.n;
        invariant to_integer(passes) + to_integer(iter.n) == to_integer(n);
        maintain by {
            if 0u32 < iter.n {
                mark iteration;
                have iter.n != 0u32;
                have passes <= 4294967294u32;
                step_until(loop.back_edge);
                have to_integer(iter.n) == to_integer(at(iteration, iter.n)) - 1;
            } else {
                have iter.n == 0u32;
                step(); step(); step();
            }
        }
    }
    step_until(function.exit);
    close();
}
```

[`design/charon-trial/user-iterator`](https://github.com/clicklang/click/blob/master/design/charon-trial/user-iterator/countdown.click)
proves the count of a countdown's passes and the last value it yields.
Generic iterators, iterator adapters over a crate iterator and a `next`
reached through a trait object remain outside this subset.

## Moves and drops

[`examples/rust-move-drop/guard.rs`](https://github.com/clicklang/click/blob/master/examples/rust-move-drop/guard.rs)
constructs a guard, moves it, changes borrowed storage, and returns through two
paths. Its checked `Drop` contract restores the original storage value. The
caller proves the result was captured before cleanup and that the storage was
restored on both paths.

A function returns its value directly when nothing runs between computing it
and returning. When a drop runs in between, the value is held in a local named
`result`, which a proof reads before the exit as any local
([magic variables](magic-variables.md#result)).

Local non-Copy structs support whole-value construction and moves, scope and
early-return cleanup, conditional initialization/moves, and explicit
`std::mem::drop`. Structs can have lifetime parameters and a local `Drop`
implementation. The compiler selects drop order and drop flags through its
ULLBC control flow; Click does not reconstruct cleanup
from source scopes. Destructor bodies require verified sidecar contracts.

The imported MIR is drop-elaborated, so rustc has already decided which
values are live at each move, read and drop. A move copies the struct's fields
into its destination and a drop runs its destructor; Click adds no live flags
of its own, so no generated name appears in a proof's state or a step's
frontier. The compiler places each drop on the paths where its value is
still live, as in a branch that moves a guard and one that keeps it.
Struct storage uses
existing checked stack allocation and typed field loads/stores. Moving a reference field carries the same borrowed address; it
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
complete Rust borrow protocol or infer ownership contracts from Rust types.

The adapter supports moving a reference field out of a plain local struct.
It still excludes general partial moves with cleanup, nested owned fields,
nested aggregate arguments or returns, unstructured control flow, heap owners
other than the [`Box`](#boxes) and a [`Vec`](#vec-values) of scalars, and panic
unwinding. Arithmetic, owned values, and loops use the
same native body representation; there is no whole-function coverage switch.

```console
cargo run --bin click -- import lock examples/rust-move-drop/guard.click
cargo run --bin click -- verify examples/rust-move-drop/guard.click
cargo run --bin click -- import lock examples/rust-field-borrow/guard.click
cargo run --bin click -- verify examples/rust-field-borrow/guard.click
```

## Boxes

A `Box<R>` of a crate struct `R` is the address of an allocation it owns:
its contents, `*b`, are an `R`, and `b.field` reads and writes through it.
`Box::new` and the box's drop are calls of the library's
[`Box<T>` contracts](library/index.md#boxt), instantiated at `R`:
`Box::new` states `allocates(result, sizeof(T)); produces *result;` and
`ensures *result == x;`, and `Box::drop` consumes `allocation(b, sizeof(T))`
and `uninitialized(*b)`.

`Box::new(r)` moves the record `r` into a new allocation and returns its
address; `Box::new(R { a, b })` builds the record in a local first.
`allocates` makes the box a block no earlier pointer reaches, as `malloc`'s
result is ([Fresh allocations](language/c.md#fresh-allocations)), so a
field the proof knows keeps its value across the caller's later stores.
Allocation failure aborts the process, so `Box::new` returns only a non-null
box. The compiler places the drop: a box of a struct with drop glue calls the
glue on the contents first, then `Box::drop`, which needs only the box's
storage, initialized or not, and frees it. An `Option<Box<R>>` drops through
`Box::drop` when it is `Some`. A struct with fields of an abstract type `T`
has a symbolic layout, and `Box::new` and `Box::drop` are instantiated at it
as at any struct.
[`design/charon-trial/boxes`](https://github.com/clicklang/click/blob/master/design/charon-trial/boxes/boxed.rs)
verifies

```rust
pub struct Cell { value: u32, }
pub fn boxed(x: u32) -> u32 {
    let mut b = Box::new(Cell { value: x });
    b.value = b.value + 1;
    b.value
}
```

against `requires x < 100; ensures result == x + 1;` by running the body
and closing the goal.

An `Option<Box<R>>` is the box's address, or null for `None`. `Some(b)` and
`None` make one, a `match` tests it for null and moves the box out of `Some`,
and its drop frees a `Some` box (freeing null has no effect).
[`design/charon-trial/option-boxes`](https://github.com/clicklang/click/blob/master/design/charon-trial/option-boxes/options.rs)
verifies `maybe`, which boxes a `Cell` only when asked and matches on the
option, and `dropped`, whose possibly-`Some` option is dropped at scope end.

`o.take()` is the library's `mem::replace(&mut o, None)`. On an option of a
scalar, and on the referent of a `&mut Option<T>`, it calls the library's
[`Option::take<T>`](library/index.md#optiontaket) contract through its
reference. On an option of a box, where the borrow the compiler takes for the
call serves only the call, the exporter checks the callee is the library's own
`Option::take` and lowers `t = o.take()` to `t = o; o = None`: the box moves
into `t`, so it is freed once, with `t`. That rewrite is a
[departure](../concepts/library-interfaces.md#where-the-implementation-departs-from-this).
In a sidecar an option of a box's `None` is null and `Some(b)` is `b`:
`self.slot == Option<Box<box_fields::Cell>>::None` reads as `self.slot == 0`.
[`design/charon-trial/option-take`](https://github.com/clicklang/click/blob/master/design/charon-trial/option-take/take.click)
verifies `taken`, which takes a boxed `Cell` and finds the option `None`
after, `taken_twice`, whose second `take` finds `None`, `scalar_taken`, and
`take_param(o: &mut Option<u32>) -> Option<u32>` with `ensures result ==
old(*o);` and `ensures *o == Option<u32>::None;`.

A crate struct may hold a box or an option of one in a field, as the box's
address, when the struct lives behind a reference. Owning the field owns what
its value holds, its [type resource](#type-resources): in
[`design/charon-trial/box-fields`](https://github.com/clicklang/click/blob/master/design/charon-trial/box-fields/holder.click)
`Holder::read(&mut self) -> u32` takes the box out of `self.slot` and reads
it, and verifies `owns self.slot; ensures old(self.slot) != 0 implies result
== old(self.slot.value); ensures old(self.slot) == 0 implies result == 0u32;
ensures self.slot == 0;` with no proof. `Holder::put(&mut self, x)` takes
the old box, assigns `Some(Box::new(..))`, frees the old one at scope end, and
verifies `ensures self.slot != 0; ensures self.slot.value == x;`. Assigning a
box field first drops its old value in place, which is the drop of that value
moved out. Removing `owns self.slot;` is refused at the field's first read
(``missing resource fact `views self.slot` ``).

### Type resources

A type resource is the resource a value of a type holds: holding a value of
the type as a resource holds it. The library declares `Box<T>`'s with the
`type` keyword, `type Box<T> { owns allocation(self, sizeof(T)); owns *self;
}`, where `self` is the box, its address
([`Box<T>`](library/index.md#boxt)). An `Option<Box<R>>`, the box's address
or null, holds its box's when it is not null, as if declared `if self != 0 {
owns Box<R>(self); }`. A sidecar declares no type resource of its own; a
`type` declaration the library does not make is refused.

Each one is an ordinary resource, named by its type applied to the value,
`Box<box_fields::Cell>(p)` or `Option<Box<box_fields::Cell>>(self.slot)`,
and every resource rule applies: `fold`, `unfold`, `owns`, `consumes` and
`produces` take it. A contract clause `owns self.f;` on a field of a box or
an option of one of a struct with no box fields of its own also consumes the
field's entry value's type resource and produces its exit value's, since the
value may change. The implicit closer unfolds and folds them where the
program reads and writes through them, and where a claim reads the field's
contents at entry, `old(self.slot.value)`, it splits on the resource's own
condition at entry, `if self.slot != 0 { unfold(...); ... } else { ... }`,
which `click expand` writes. Recursive structs, a list's node holding
`Option<Box<Node>>`, have no derived type resource yet and state theirs as a
named resource, as below.

A struct may hold a box of its own type, `Node { value: u32, next:
Option<Box<Node>> }`. Dropping a box of such a struct runs the struct's drop
glue on it before the free, `if (b) glue(b); free(b);`: the compiler's glue
drops the struct's box fields, so it frees the nodes after this one in turn,
recursively. The glue has no source function, so the sidecar states its
contract in an `impl Destruct for R` block, with a `fn drop_glue(&mut self)`
whose contract consumes the resources its box fields own and whose proof
frees them; a recursive glue ranks its recursion by the resource it consumes.
[`design/charon-trial/recursive-drop`](https://github.com/clicklang/click/blob/master/design/charon-trial/recursive-drop/list.click)
verifies `impl Destruct for recursive_drop::Node`'s `drop_glue` with `owns
self.value; owns self.next; consumes rest: nodes(self.next); decreases rest;`,
proved by splitting on `rest.values`, unfolding `rest`, and running the rest
of the body,
over a resource `nodes(p)` whose `List<u32>` field holds the values, owning
each node's allocation, the node, and `nodes(p.next)`. With it, a stack's
`push`, which takes the head and assigns `Some(Box::new(Node { value, next
}))`, and `clear`, which assigns `None` and so frees every node, verify.

A struct holding a box may be owned by value. Its drop calls its glue, and the
glue's contract takes the resource the caller holds over the struct's box
fields: the call binds the one instance of that resource the caller owns, so
the compiler-placed drop needs no proof step. The caller comes to hold it as
any resource, from a contract: `Stack::new() -> Stack` states `produces after:
nodes(result.head);`, a resource over the returned struct's field, and in the
fixture's `pushed`, `let mut s = Stack::new(); s.push(x); x` verifies by
running its body, `push` taking and returning the list and the drop of `s` freeing
it. A drop whose caller holds no such resource is refused at the glue call.

`?` reads an option of a box as it does one of a scalar, and moving a field
out of a box, `self.head = node.next`, leaves the box to be freed without its
glue: the compiler calls `<Box<R> as Drop>::drop(&mut node)`, which the
exporter checks is the library's own and lowers to the free alone. The
fixture's `pop`, `let node = self.head.take()?; self.head = node.next;
Some(node.value)`, verifies `ensures result == first(old(before.values));`
and `ensures after.values == rest(old(before.values));`, splitting on the
list and refolding the tail, and `round_trip`, `let mut stack = Stack::new();
stack.push(x); stack.pop()`, verifies `ensures result ==
Option<u32>::Some(x);` by running its body and one unfold of `first`.

A box, or an option of one, also moves into a function and out of one by
value, with its allocation and its struct: a sidecar writes the type as Rust
does, `Box<boxed::Cell>` or `Option<Box<boxed::Cell>>`, and it is the
struct's address. A function a box moves into owns it and frees it at its
drop, so its contract consumes what the box owns; a function a box moves out
of produces it. A function that returns a box it made states `allocates`
only when every box it returns is new; one that may return a box it was
given states `produces allocation`.
In the fixture, `make(x) -> Box<Cell>` states `produces allocation(result,
sizeof(boxed::Cell)); produces *result; ensures aligned(result, 4); ensures
result.value == x;`, `read(b: Box<Cell>) -> u32` consumes them, and
`through(x)`, `read(make(x))`, verifies `ensures result == x;` by running
its body and closing the goal. An option of a box crosses a call under a resource that owns the
cell only for `Some`, `resource cell_box(p: *mut boxed::Cell) { field value:
Option<u32>; match value { Option::None => { fact p == 0; }, Option::Some(v)
=> { owns allocation(p, sizeof(boxed::Cell)); owns *p; ... } } }`: `maybe`
folds it on each side of its `if`, `value_or` unfolds it on each side of its
`match`, and `maybe_through` verifies `value_or(maybe(x, make), 0)` by cases
on `make`. A `read` that keeps what it consumed (`owns` for `consumes`) and a
`make` that does not produce its allocation are refused.

Import refuses a reference to a box or to an option of one ("reference to a
box parameter or result"), a box of a record with a `Drop` implementation
("box of a record with a destructor"), and a struct with both a `Drop`
implementation and a box field ("destructor of a struct holding a box").

## Option values

A Rust `Option<T>` of `i32`, `u8`, `u16`, `u32`, `usize` or `bool`, or in
generic code of the function's own type parameter, is a value of the library's [`spec enum Option<T>`](library/index.md#clickoption) at `T`,
imported like a crate enum (see [Enums and `match`](#enums-and-match)): `Some(x)`
and `None` construct it, and `match`, `if let` and `matches!` on it step and
split as on any enum. A sidecar writes the type as Rust does, `Option<u32>`,
and a parameter or `result` of that type is an `Option` value: compare it with
a constructor, or `match` on it.
[`design/charon-trial/option-values`](https://github.com/clicklang/click/blob/master/design/charon-trial/option-values/options.click)
verifies `some_if`, whose contract is `ensures make implies result ==
Option<u32>::Some(x);` and `ensures make == false implies result ==
Option<u32>::None;`, and `or_zero`, whose contract is `ensures result ==
(match o { Option::Some(v) => v, Option::None => 0u32 });`, each by running
its body and closing the goal, and a caller, `round(x) = or_zero(some_if(x,
true))`, whose `ensures result == x` follows from the two contracts by
`close()`. A fact
the caller learns that matches on a value it already knows is a constructor,
`result == match o { .. }` after `o == Option::Some(x)`, is also kept reduced
at that constructor, `result == x`. In the same fixture `flag(o: Option<bool>)`
matches an `Option<bool>`, and the generic `wrap<T: Copy>(value: T) ->
Option<T>`, with `ensures result == Option<T>::Some(value);`, and
`unwrap_or<T: Copy>(o: Option<T>, default: T) -> T` are verified once with `T`
abstract; a caller at `i32`, `unwrap_or(wrap(x), 0)`, uses both contracts at
`Option<i32>`. A generic function's type parameters name the program's types
in its whole contract, so `Option<T>` in an `ensures` clause is the same type
as in its signature.

`o?` on an `Option` returns `None` from the function when `o` is `None` and
otherwise yields `Some`'s payload: the exporter checks that the compiler's
`branch` and `from_residual` calls are the library's own `impl Try for
Option<T>` and `impl FromResidual<Option<!>> for Option<T>`, then lowers them
to the `match` they define, for an option of a box too
([boxes](#boxes)). In the fixture `plus_one(o: Option<u32>) ->
Option<u32>`, `let v = o?; Some(v + 1)`, verifies
`ensures result == (match o { Option::Some(v) => Option<u32>::Some(v + 1u32), Option::None => Option<u32>::None });`
under `requires match o { Option::Some(v) => v, Option::None => 0u32 } <
4294967295u32;`, and the generic `same<T: Copy>(o: Option<T>)`, `let v = o?;
Some(v)`, verifies `ensures result == o;` once with `T` abstract. A `match` on
a local, a call's result or the option `?` reads, splits like one on a
parameter, and its arms also learn the constructor for each value a premise
equates with it, so `read_passed`, a `match` on `passed(o)` whose contract is
`ensures result == o;`, proves a postcondition written about `o`. Each of
several `?`s in a function returns `None` through the same tail, which the
importer lowers in each arm that reaches it, as a C early `return`: the
fixture's `sum(a, b)`, `let x = a?; let y = b?; Some(x + y)`, verifies its
nested `match` contract after splitting on `a` and `b`. Options of other
payloads and `Option` methods other than [`take`](#boxes) and
[`unwrap_or`](#core-library-methods) remain later work.

A `&Option<T>` or `&mut Option<T>` parameter, and a reference to a crate enum,
refers to one value of the enum: the contract writes `views *o` or `owns *o`
and reads, compares and matches `*o`, and `old(*o)` is its value at entry. The
body reads, writes and matches through it; a `match *o` tests a copy of the
referent taken at the match, then reads each field through `o`. A local of an
enum, of a type parameter, or of an integer or `bool` that the body borrows
with `&` or `&mut` keeps its value in its stack object, so a callee's write
through the borrow is the value the caller reads next; an enum or
type-parameter local the body never borrows keeps its value in its binding.
A proof names such a local's value by the local's name, `o`, read where the
program last wrote it, so a fact a callee's contract gives about `*o` is one
a proof can cite: in
[`design/charon-trial/held-values`](https://github.com/clicklang/click/blob/master/design/charon-trial/held-values/held.click),
`constructed` and `returned` close `result < x` by arithmetic over
`shrink`'s `size(*o) + 1 <= size(old(*o))` about the borrowed local `o`.
[`design/charon-trial/option-refs`](https://github.com/clicklang/click/blob/master/design/charon-trial/option-refs/refs.click)
verifies `take_it(o: &mut Option<u32>) -> Option<u32>`, with `ensures result ==
old(*o);` and `ensures *o == Option<u32>::None;`, `fill`, which stores
`Some(x)`, and `peek(o: &Option<u32>)`, a `match *o`; a caller `round(x)`
borrows its local `o` for `fill` and then `take_it` and proves `result == x`,
and `cleared(x)` proves `result == 0u32` after `clear(&mut o)` wrote `None`
over its local's `Some(x)`. A fact a call adds that matches on the enum behind
a reference the facts already equate to a constructor is kept reduced, as for
a variable. The same fixture borrows a local of a type parameter in
`replaced<T: Copy>` and a `u32` local in `bumped`.

## Result values

A Rust `Result<T, E>` whose `T` and `E` are each `i32`, `u8`, `u16`, `u32`,
`usize` or `bool`, a non-generic enum of the selected file, or in generic code
the function's own type parameters, is a value of the library's
[`spec enum Result<T, E>`](library/index.md#clickresult):
`Ok(x)` and `Err(e)` construct it, and `match`, `if let` and `matches!` on it
step and split as on any enum. A sidecar writes the type as Rust does,
`Result<u32, u8>`, and constructs `Result<u32, u8>::Ok(x)`; a pattern is
`Result::Ok(v)`. A `Result` of another type, such as a record, is refused by
name.

A crate enum payload is that enum's own `spec enum`: `Result<u32, ParseError>`
constructs `Result<u32, ParseError>::Err(ParseError::TooBig(x))`, a `match`
arm `Result::Err(e)` binds `e` as a `ParseError`, and a Rust `match` on
`Err(ParseError::Empty)` tests the error as it tests any enum local. So may an
`Option`'s payload be a crate enum. Enums are imported from single-file units
only ([coverage](coverage.md)).
[`design/charon-trial/result-errors`](https://github.com/clicklang/click/blob/master/design/charon-trial/result-errors/errors.click)
verifies `check`, which returns either `ParseError` variant, `forwarded`,
whose `?` returns whichever it met, `doubled`, `describe`, a nested
`match`, and `wrapped` and `unwrapped` over an `Option<ParseError>`; each
false claim mutated into the sidecar is refused
(`tests/rust_import.rs::charon_result_errors_carry_a_crate_enum`). The
callers' proofs rest on a kernel rule for an implication whose consequent the
facts make an equation of two constructors: `x == 0 implies r ==
Err(ParseError::Empty)` beside `r == Ok(v)` is `x != 0`, and `P implies
Ok(v) == Ok(x)` is `P implies v == x`.

`r?` on such a `Result` returns `r`'s `Err` unchanged and otherwise reads
`Ok`'s payload: the importer checks that the compiler's `branch` and
`from_residual` calls are the library's own `impl Try for Result<T, E>` and
`impl FromResidual<Result<!, E>> for Result<T, F>`, and rewrites them to the
`match` they define. Only a `?` whose function returns the same error type,
`F == E`, is read, where the `From::from` the library applies is the
identity; one that converts the error is refused ("`?` that converts the
error type with `From`").

`r.unwrap()` and `r.expect("...")` of a `Result` of scalars call
`Result::unwrap<T, E>` and `Result::expect<T, E>`, whose contract requires
`exists (value: T) { r == Result<T, E>::Ok(value) }` and ensures
`r == Result<T, E>::Ok(result)`; the panic on `Err` is that requirement, and
`expect`'s message is not passed. A caller that knows `r ==
Result<u32, u8>::Ok(5u32)` meets the requirement by `close()`, which takes the
known constructor's payload as the witness, and a contract that reads the
result through `match r { .. }` reduces the `match` by the call's
`r == Ok(result)`.
`r.unwrap_or(d)` calls `Result::unwrap_or`, whose contract is
`ensures result == click::rust::result::unwrap_or(r, d);`.

[`design/charon-trial/result-values`](https://github.com/clicklang/click/blob/master/design/charon-trial/result-values/results.click)
verifies `ok_if`, `or_zero` and a caller `round` composing them, `plus_one`
(`let v = r?; Ok(v + 1)`), `quarter`, whose `?` on `divide(x, 2)` feeds a
second `divide`, `error_code` (`if let Err(code) = r`), a generic `same<T, E>`
with a caller at `Result<i32, bool>`, and `must`, `must_say` and `or_default`
over `unwrap`, `expect` and `unwrap_or`; each false claim mutated into the
sidecar is refused (`tests/rust_import.rs::charon_result_values_read_as_click_results`).
Other `Result` methods, `map_err`, and `?` across error types remain later
work.

## Vec values

A `Vec<T>` of an integer or `bool` is a value of the library's primitive
[`Vec<T>`](library/index.md#rust-vectors): the sequence it holds, with no
heap buffer or capacity in the model. A sidecar writes the type as Rust
does, `Vec<u32>`, `&Vec<u32>` or `&mut Vec<u32>`, and a contract reads
`v.len()` and `v[i]`, which are `vec::len(v)` and `vec::get(v, i)` (of `*v`
for a reference). A signature that names a `Vec` brings the library module
`click::rust::vec` in, so a sidecar needs no import to use them.

`Vec::new()`, `Vec::with_capacity(n)`, `v.push(x)`, `v.len()` and `v[i]`
call external functions whose contracts Click supplies, the generic
`extern fn` blocks `Vec::new<T>` ... `Vec::index<T>` of
`library/rust/core.interface.click` written out at the element type, `Vec::push<u32>`:

- `new` and `with_capacity` ensure `vec::len(result) == 0`; the reserved
  capacity is not modeled.
- `push` owns `*v`, requires `vec::len(*v)` below `u64::MAX`, and ensures
  `*v == vec::push(old(*v), x)` together with what the library's axioms
  say of that vector: its length is one more, its last element is `x`, and
  every earlier element is unchanged. A caller therefore reads the length
  and elements after a push without citing an axiom.
- `len` views `*v` and ensures `result == vec::len(old(*v))`.
- `v[i]` views `*v`, requires `i < vec::len(*v)`, Rust's index panic, and
  ensures `result == vec::get(old(*v), i)`. The compiler reads the element
  through the reference `Index::index` returns; the importer reads the
  element itself.

Dropping a `Vec` has no effect a contract reads. A local the body borrows,
`let mut v = Vec::new(); v.push(x);`, keeps its value in its stack object,
which a proof names `v` ([held values](#option-values)).
[`design/charon-trial/vec-values`](https://github.com/clicklang/click/blob/master/design/charon-trial/vec-values/vecs.click)
verifies `single` (`result.len() == 1u64` and `result[0u64] == x` after
`Vec::new` and one push), `count`, `first` (`v[0]` under `requires 0u64 <
v.len();`), `append`, `pushed_len`, `empty_len`, `pair` over
`Vec::with_capacity`, and `second_of_pair`, which indexes a vector a call
returned; each false claim mutated into the sidecar is refused, and `first`
without its requirement is refused as the index panic
(`tests/rust_import.rs::charon_vec_values_read_as_the_library_vec`).

An element before the last after two pushes, `pair`'s `result[0u64] == x`,
needs the push contract's `forall` instantiated at that index, which `close()`
does not do on its own. A `Vec` of anything but an integer or `bool`, a
`Vec` field or `Vec` parameter taken by value and then borrowed, `&v` as a
slice, iteration, and the other `Vec` methods remain later work.

## Enums and `match`

A non-generic enum declared in the selected file is the `spec enum` of the
same name, and the import declares it for the sidecar: `Shape` below is
`spec enum Shape { Circle(u32), Rect(u32, u32), Empty }`. Variant fields may be
the supported integers or `bool`. A struct variant's fields are positional
in the sidecar, in declaration order: `Shape::Rect { width, height }` is
`Shape::Rect(width, height)`. Contracts use the enum's constructors, equality
and spec-level `match`:

<!-- verified-example: tests/fixtures/rust-verification/enums.click -->
```click
verifying "shapes.rs";

fn grow(s: Shape) -> Shape {
    requires match s { Shape::Circle(r) => r, Shape::Rect(w, h) => 0u32, Shape::Empty => 0u32 } < 4294967295u32;
    ensures result == match s {
        Shape::Circle(r) => Shape::Circle(r + 1u32),
        Shape::Rect(w, h) => Shape::Rect(w, h),
        Shape::Empty => Shape::Empty,
    };
}
```

Enum values pass by value as parameters, returns and locals, and are built
by constructor expressions. A `match` on an enum, `if let`, and `matches!`
lower to an `if` chain whose conditions test the variant (`s is Circle` in
diagnostics); a field read selects its field from the variant its arm
established. A `match` on an integer, including or-patterns and a wildcard
arm, lowers to an `if` chain of equality tests.

`if`, integer `match` and enum `match` step and split alike. `step()` enters
an arm whose variant the facts decide. Where the variant is open, `step()`
refuses and names the split: a proof `match` on the value, one arm per
variant, with each field bound as `<local>_<variant>_<index>` (variant in
snake case, made fresh against the function's locals):

```text
`step` reached a Rust `match` of `s`, whose variant is not known here; each variant is its own proof arm. Write `match s { Shape::Circle(s_circle_0) => { ... }, Shape::Rect(s_rect_0, s_rect_1) => { ... }, Shape::Empty => { ... } }` here, or end the script here and let its implicit tail split it
```

Leaving the split to the implicit tail that ends every proof script means the
tail inserts that proof
`match` and runs each arm to the function exit, as it splits at an undecided
C condition; expansion shows it. An arm that learns `s == Shape::Circle(s_circle_0)` also gets every fact
that matches on `s`, reduced at that constructor, so a requirement
`match s { Shape::Circle(r) => r, ... } < 4294967295u32` becomes the citable
`s_circle_0 < 4294967295u32` for the `+ 1` panic check. A written proof
`match s { Shape::Circle(r) => { ... }, ... }` placed before the C does the
same with its own binders. A scalar spec `match` retains its symbolic term
while its scrutinee is symbolic, even when the facts identify a constructor.
Signed arithmetic in an arm contributes a definedness obligation guarded by
that constructor, universally quantified over its payloads. Only a selected
arm owes that obligation; checking reduces the term using the branch facts.

Not yet supported: generic crate enums and options other than the
[scalar options](#option-values) and the `Option<Box<R>>` above, enums declared in
crate units, enum fields of other enum or struct types,
enums in struct fields, and reducing a callee's `match` precondition over a call result
whose constructor the caller knows only from the call's postcondition
(`perimeter(square(side))`).

The [enum example](https://github.com/clicklang/click/tree/master/examples/rust-enums)
covers construction, field reads, a requirement instantiated per arm,
`matches!`, `if let` with a written proof `match`, and an integer `match`.

## Borrow and proof boundary

rustc establishes source type and borrow legality, and Click trusts it: the
importer admits only safe Rust (it refuses `unsafe` functions, unsafe calls and
raw pointers other than a `Box`'s), so every imported function's borrows have
already been checked. Click checks the functional contract and the memory
access obligations of the extracted execution. Borrowed references carry no
allocation or deallocation authority.

A reference parameter's type grants authority over its referent (see
[Signatures in Rust syntax](#signatures-in-rust-syntax)); every other resource
a contract uses is written. At a call, the caller lends what the callee's
contract names, and that lending is also how the caller knows the callee
writes nothing else it holds.

Inside a body, a reference is the address of the place it borrows: `&mut x`
and `&x` are pointers to `x`'s storage, a reborrow `&mut *r` is the same
pointer, and reads and writes through any of them are reads and writes of that
storage. Writes through a child are observed through its parent. Click does
not re-check when a borrow ends or whether a parent is reused while a child is
live; rustc has. A reference may stay live across calls, loops, branches and
returns
(`design/charon-trial/gate-fixtures/reference-across-call`).

The trusted boundary includes the pinned compiler, exporter, semantic artifact,
and its translator. The lock detects stale or changed inputs; it is not an
attestation against somebody deliberately replacing the artifact and its lock.
Tests distinguish invalid Rust rejected by rustc from false functional claims
rejected by Click, and check the ordinary CLI and proof expansion path.

### Scalar recursion

A scalar recursive function can declare `decreases n;` for an integer
parameter. The measure is checked at each recursive call, using the value
of the argument even when checked Rust arithmetic introduces a MIR temporary.
The next measure must be nonnegative and strictly smaller. An unchanged
argument is refused. This uses the same call-ranked expression measure for
`i32` and `i64` parameters.

`tests/fixtures/rust-verification/recursive-countdown/r.click` verifies the
unchanged `countdown(n - 1)` functions at both widths;
`tests/rust_import.rs::rust_recursive_countdown_refuses_unchanged_argument`
keeps the negative control.

The importer profile retains historical opaque identity tags in its manifest
and existing project locks. Those tags are compatibility data. Renaming
verifier implementation types or documentation does not change the frontend semantic profile. Program
source files remain covered by their import-lock digests and require an
explicit lock refresh when changed.
