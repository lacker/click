# `click import`

Compiler imports let a sidecar verify the C selected by a configured compiler
preprocessor. Click still parses and lowers the resulting C and independently
checks its proofs. This mode is explicit and separate from the existing bounded
source-bundle preprocessor. The same command also refreshes the preliminary
typed C++ artifact described below. [Language coverage](../coverage.md) summarizes
what the C and C++ import paths admit.

```text
usage: click import lock <sidecar.click>
```

## Interface boundary

Verification runs against interfaces that Click defines; it needs no compiler,
system headers, or frontend toolchain.

- **Standard library interfaces live in Click.** A header such as
  `<pthread.h>`, `<stdatomic.h>`, `<limits.h>`, `<string.h>`, or `<stdlib.h>`
  describes a library the program calls. Click supplies its own declarations
  and a specification of each call; see the
  [C system headers](../language/c.md#system-headers). Proofs assume a C
  library that implements Click's interfaces as specified. Click does not
  import or verify a platform's library headers or bodies to supply an
  interface. A compiler import searches the same headers; see
  [Click's system headers](#clicks-system-headers).
- **Compiler import is for the program's own code.** Use it when the build
  selects that code: its `-I` and `-D` flags, or headers that carry code
  under verification, such as Linux's own headers with their structs, inline
  helpers, macros, and `CONFIG_*` selection. Calls that code makes to
  anything outside it still use Click-side contracts.
- **A language frontend is a separate case.** Click has no C++ or Rust type
  checker of its own, so the pinned Clang 19 exporter and Charon are accepted
  frontends. Each runs once at `click import lock`; verification loads the
  artifact offline.
- **The C++ standard library is axiomatic.** It is mostly header code that
  Clang must parse to type-check a program, so the real headers are parsed,
  but none of their code is trusted or verified: a call into a system header
  is checked against Click's contract for it. See
  [the C++ standard library](#c-standard-library).
- **The default workflow needs none of it.** `click verify` on plain C needs
  no compiler or system headers.

## Configure and lock an import

For `main.click`, create `main.click.import.json`. The configuration lists the
logical C sources named by the sidecar's `verifying` declarations, their compiler
inputs, and the output artifacts. For example:

```json
{
  "schema": 1,
  "target": "x86_64-linux-kernel",
  "compiler": "/usr/bin/gcc",
  "working_directory": ".",
  "environment": {
    "allow": {
      "PATH": "/usr/bin:/bin",
      "LC_ALL": "C",
      "SOURCE_DATE_EPOCH": "0"
    }
  },
  "sources": [
    {
      "logical_source": "main.c",
      "path": "main.c",
      "args": ["-DVARIANT=1", "-isystem", "configured"],
      "artifact": "main.i"
    }
  ]
}
```

The working directory is relative to the configuration file. Source and include
paths are interpreted in that working directory; artifact paths are relative
to the configuration file. Logical source paths identify translation units and
must match the sidecar, independently of the original header filenames used by
diagnostics.

Run `click import lock main.click` to create or explicitly refresh the configured
artifacts and `main.click.import.lock.json`. Then run `click verify main.click`.
The configuration's presence selects compiler mode for verification and its
associated proof tools. An invalid configuration or missing lock is an error;
it does not fall back to source-bundle mode.

Verification loads the recorded C artifact without executing or locating the
configured compiler. The artifact and version-3 lock can move to another host
with the same config bytes, C source, and project-local included headers. Loading
checks their hashes, the artifact bytes and size, the target, the recorded
toolchain/invocation identity, and the source projection identity. System
headers used during preparation are identified in the lock but need not be
installed on the verification host. A version-1 C lock must be refreshed. A
version-2 lock, written before compiler imports searched Click's system
headers, still loads under its recorded identity: its preparation opened none
of them. Refreshing it writes version 3.

This verifies the **prepared snapshot**. A change to the C source or an opened
project-local header is rejected during loading. A change to external headers,
or the appearance of a previously absent header selected by `__has_include`,
does not silently change that snapshot; run `click import lock` in the selected
toolchain environment to prepare a new one. The lock is a consistency record,
so publication and provenance of a native platform artifact still need a
trusted preparation process.

Lock creation is source preparation, not proof verification. The C parser can
still reject an unsupported construct when a proof tool loads the prepared
translation unit. No C declarations, function bodies, storage, attributes, or
assembly are silently deleted to make an import pass.

## Preliminary C++ semantic artifact

The preliminary C++ frontend boundary accepts one C++20 translation unit
selected by exactly one entry in a JSON compilation database, with one
selected free function or ordinary method and the uniquely named definitions
reachable from its supported direct call statements. In the baseline profile,
exceptions are disabled and every selected or reachable function must declare
`noexcept`. A second, deliberately smaller profile may retain the compilation
command's enabled exception mode: free functions and ordinary methods may omit
`noexcept`, but the closed reachable graph must contain only Click's checked
normal-returning operations. This profile permits borrowed trivial records,
while local object construction remains outside it.
The selected definitions may be written in the `.cpp` translation unit or in
one configured `.h` project header included by that translation unit. All
lowered declarations and source spans must come from that one logical source.
The linear reference fixture is:

```cpp
int increment(int& value) noexcept {
    value = value + 1;
    return value;
}
```

Its baseline import configuration explicitly sets `"language": "c++"`, the
standard to `c++20`, target to `x86_64-unknown-linux-gnu`, exceptions and RTTI to false,
and paths for the pinned exporter, compilation database, working directory,
`.cpp` translation unit, logical source, selected function, and semantic
artifact. These booleans may also be true for a supported normal-only
reachable graph; the observed Clang profile must match the configuration.
`click import lock` executes the repository-owned Clang 19.1.7
LibTooling exporter with that entry and records the database bytes, exact parsed
command and directory, source, explicitly declared reachable-declaration
dependencies, every file Clang lexes while preprocessing the translation unit,
exporter, semantic profile, artifact, and configuration identities. Reachable
declaration spans outside the logical source must name one of the relative
dependencies. The broader preprocessor inventory also covers headers whose
declarations are not lowered. For each opened file the lock records its
accessed path, resolved target, and content hash. Refresh repeats the export
across a bounded inventory snapshot; offline loading rejects changed contents
or symlink targets without running Clang.
The configured working directory is also the dependency root: it may contain
the project source tree and a Linux sysroot while the selected CMake
compilation command runs in a separate build directory. Dependencies retain
paths relative to that root, not to the build directory. The Bitcoin Core
`MoneyRange` integration in `integrations/bitcoin-core-money-range/` uses this
arrangement on macOS.

```json
{
  "schema": 6,
  "language": "c++",
  "standard": "c++20",
  "target": "x86_64-unknown-linux-gnu",
  "exceptions": false,
  "rtti": false,
  "exporter": "target/cpp-exporter/click-cpp-exporter",
  "compilation_database": "compile_commands.json",
  "working_directory": ".",
  "source": "increment.cpp",
  "logical_source": "increment.cpp",
  "dependencies": [],
  "function": "increment",
  "artifact": "increment.cpp.click-cpp.json"
}
```

The database must resolve the configured translation unit to exactly one
command using the pinned Clang driver and the configured C++20, target,
exception, and RTTI profile. Missing or ambiguous entries and mismatched driver
or semantic profiles fail refresh locally. When `logical_source` names a
header, the importer resolves and hashes that file separately from the `.cpp`
translation unit. Offline loading rejects a missing or modified selected
header. Textually included project, sysroot, and Clang resource headers are
inventoried even when they lie outside the configured dependency root.
Response files, PCH, modules, VFS overlays, and arbitrary Clang pass-through
options are rejected because their hidden inputs are not inventoried.

For a compilation command with exceptions enabled, the config instead sets
`"exceptions": true`; the observed Clang profile must agree. The semantic
artifact records `exception_behavior: "normal_only"` independently from each
function's `declared_noexcept` value. This is not exception handling support:
reachable `throw`, `try`/`catch`, unresolved calls, and local object construction
are rejected locally. Borrowed references to the supported trivially destructible
record may use its checked fields and ordinary methods. Because the artifact contains the complete supported
direct-call closure and has no throwing operation, ordinary verification may
check its normal behavior without inventing an exceptional proof outcome.
An RTTI-enabled profile also permits those borrowed records; this does not add
virtual dispatch, `typeid`, or `dynamic_cast` semantics.

The separate `"exception_behavior": "scalar_int32"` config requires
`"exceptions": true`. Its locked artifact may contain a source `throw` of a
typed `int` payload in an object-free function; the importer lowers that node
to Click's checked exceptional statement outcome. A Click `throws int32`
signature must still declare the exception, and normal and exceptional
postconditions are proved separately. Reachable direct calls can propagate
that exception while normal scalar statements continue. One object-free
`try` with exactly one named by-value `catch (int name)` is also supported.
The handler binds the thrown payload and resumes from the thrown state, so a
caller can catch a verified helper's exception without declaring `throws`.
One narrow unwinding case is also supported: a `try` block may first
construct destructible automatic guards, then call a potentially throwing
helper. Each guard's public, non-virtual constructor and destructor must be explicitly
`noexcept`; the destructor runs on both normal and exceptional exits before
the handler observes state. The constructor's Click contract must establish
any object invariant required by the destructor that is not already available
from the checked execution state. The `cpp_one_guard_unwind` and
`cpp_two_guard_unwind` mdtests verify both outcomes with one and two guards;
the guards are destroyed in reverse construction order.
The importer still rejects nested handlers, catch-all or non-`int` handlers,
other local declarations inside either block, guards constructed after the call, returns
from a guarded `try`, `noexcept` free functions (whose termination behavior is
not modeled), and broader exceptional resource transfer. This is not general
C++ unwinding support or an exception-ABI proof. Clang's typed
source semantics and the compiler/runtime implementation remain the trust
boundary. The config, artifact, and lock keep
it distinct from both the exception-disabled baseline and exception-enabled
`normal_only` profile.

Loading through the C++ library boundary subsequently validates the translation
unit, selected logical source, compilation database, lock, and typed artifact
without locating or running Clang. This separation is intentional: compiler
execution belongs to explicit refresh. Changing either source or any command,
including a flag that leaves the selected AST unchanged, invalidates the lock.
The library lowers this exact artifact directly to the kernel execution
vocabulary without generating C text or invoking the C parser. An `int&` or
`const int&` becomes an address-valued parameter with its pointee qualification
preserved. Reads become typed loads, while only the mutable reference permits a
typed store; signed addition retains the kernel's existing overflow check. The
lowered value remains paired with the immutable semantic artifact so Clang
declaration identities and source spans are not discarded.

The sidecar declares a reference as a reference, and its name is the object
it refers to:

<!-- verified-example: examples/basic-cpp/increment.click -->
```click
verifying "increment.cpp";

int32 increment(int32& value) {
    requires value < 2147483647;
    owns value;
    ensures value == old(value) + 1;
    ensures result == value;
} by {
    execute();
    simp();
}
```

`owns value` owns the referent, `value` reads it, and `&value` is its address,
for a contract that says two references alias (`requires &a == &b;`) or that a
stored pointer points at one. A struct reference names its fields as
`state.field`. Writing `int32* value` for an `int&` is a signature mismatch
that names both spellings; a C++ `int*` parameter stays a pointer. A member
function's receiver is the pointer `this`, as in C++: `this->fee`,
`owns *this`.

Native `int&` and `const int&` results use `int32&` and `const int32&`
sidecar results. `result` reads the returned referent; `&result` identifies its
address. For example, a helper returning an existing reference parameter can
state `ensures &result == &value;` without reading backing storage. A value
claim such as `ensures result == old(value);` additionally needs a resource
for that storage. Returning an alias grants no new ownership or write authority.
Reference and pointer results remain distinct during signature checking, and
const qualification is preserved through modular calls and result temporaries.

The result profile returns existing integer reference parameters, including
direct call forwarding, and binds references through supported integer pointer
dereferences. New bindings use the shared kernel's checked object address:
the complete referent must occupy live storage, excluding null, expired and
one-past addresses. This check neither reads nor initializes the referent and
grants no access authority. Automatic `int&` and `const int&` locals can bind
existing references, supported pointer dereferences, and direct calls with
matching native reference results. Assignment through a mutable reference local
writes its referent; it does not rebind the alias.

Native element references are `int&`, `unsigned int&`, `unsigned char&` and
`std::byte&`, each possibly `const`, written `int32&`, `uint32&` and `uint8&`
in the sidecar. They are admitted as parameters, results and locals. A call
that returns one can also be read or written directly, as in `return s[0];`
and `s[0] = v;`. A read is a typed load of the returned address and needs a
resource for the referent. A write needs a mutable referent and owns it; its
value must be free of calls and is read before the call, as C++17 sequences
an assignment's right operand first. Compound assignment through a returned
reference remains unsupported. Ending the local binding does
not end the backing object's lifetime. References to local objects, temporary
lifetime extension, rvalue references and nested reference declarations remain
unsupported.

A proof names a reference local as it names a reference parameter. For
`int& r = value;`, `r` is the referent, as in `have r == 1;`, and `&r` is its
address, as in `have &r == &value;`. `r[0]` is refused with the spelling to
write. Binding a reference is not an assignment, so `assignment(r, N)` is
refused; a store through `r` is selected by its statement.

Nothing here translates the C++ body to C. The sidecar signature is
checked against the selected typed Clang declaration, while proof execution
uses its direct kernel lowering. `click verify`, `click profile`, `click
expand`, and `click audit` all load the same locked C++ input; verification and
rewritten-proof checks remain offline after refresh.

The sibling `branch-return` integration fixture additionally checks by-value
`bool`, a braced `if`, fallthrough, and an early return. The semantic artifact
retains the structured branch and both return edges; Click does not flatten it
into C text. The `const-reference-alias` fixture writes through an `int&` and
reads through an aliased `const int&`, using one explicit `owns` resource.
C++ `const` restricts access through that reference; it does not create a Click
`views` resource or imply that aliases cannot write. Supported parameters are
currently by-value `bool` or signed/unsigned 32/64/128-bit integers, native element references,
mutable `int*`, `unsigned int*` or `unsigned char*`, one `const` signed-64 reference, and mutable or const references
to supported simple record types with distinct proof-facing names. Selected functions return `int`,
signed/unsigned 64/128-bit integers, `unsigned int`, `unsigned char`, `bool`, mutable `int*`, `unsigned int*` or `unsigned char*`,
native element references, or `void`.

Free and ordinary member functions also admit mutable by-value simple-record
parameters with trivial copying and destruction, without base subobjects.
Clang-resolved trivial copy arguments retain a distinct `record_copy` artifact
node, nominal type, lvalue projection, and span. The shared aggregate model
copies the descriptor into separately owned parameter storage; pointer fields
keep their original backing allocation and do not grant access to it. Moves,
prvalue arguments, user-defined copy bodies, and nontrivial destruction remain
refused. Artifact schema 57 requires refreshing older locks.

Contracts cannot observe a modified private parameter object as though it were
the caller's original object. Entry-state pointer values can still name
backing effects: `load_int32(old(value.data))` reads current memory through the
entry pointer, while `old(load_int32(value.data))` reads entry memory.

The `int64-predicate` fixture is the first narrow bridge toward Bitcoin Core's
`MoneyRange`: Clang retains the declaration identity and source span for a
direct `typedef long CAmount`, lowers `const CAmount&` as a const `int64*`,
retains the implicit `int`-to-signed-64 conversion of zero, and returns the
Boolean result of signed `>=`. Its exact all-input contract states the result
with a conditional expression and verifies offline:

<!-- verified-example: tests/fixtures/cpp-verification/int64-predicate/money_nonnegative.click -->
```click
verifying "money_nonnegative.cpp";

bool money_nonnegative(const int64& nValue) {
    owns nValue;
    ensures result == (if old(nValue) >= 0i64 { 1 } else { 0 });
} by {
    if nValue >= 0i64 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
```

The `constexpr-coin` fixture includes a pinned fixture-owned `<cstdint>`,
retains the ordered `CAmount` to `int64_t` alias chain across that locked
dependency, and imports one namespace-scope `static constexpr CAmount COIN =
100000000`. A reference to `COIN` carries its Clang declaration identity while
direct lowering uses its checked signed-64 evaluated value. The artifact also
retains the literal initializer and rejects disagreement between it and the
evaluated value. Offline loading needs neither Clang nor the exporter, but it
does rehash the declared header dependency.

The `constexpr-max-money` fixture extends that boundary to exactly one ordered
constant dependency: `MAX_MONEY = 21000000 * COIN`. The artifact retains both
declaration identities and the signed-64 multiplication tree, requires `COIN`
to precede `MAX_MONEY`, recomputes the result with checked multiplication, and
compares it with Clang's evaluated value. Direct lowering still substitutes the
validated `MAX_MONEY` value; it does not add runtime multiplication to the
kernel boundary. A second selected function in that fixture imports signed
64-bit `value <= MAX_MONEY`, retains the distinct Clang `<=` operator, and
lowers it directly to the kernel's inclusive signed comparison.
The third selection has the synthetic `value >= 0 && value <= MAX_MONEY`
shape. It retains Clang's built-in logical-and node and both comparisons,
then lowers to the kernel's left-to-right short-circuit operation with a
`bool` result. Its exact inclusive-range contract verifies offline; a false
upper-boundary contract fails.

These fixtures do not claim the host C++ standard library: their header is a
pinned input containing only the needed `int64_t` typedef. Mutable or
non-`constexpr` globals, undeclared header dependencies, broader or unordered
constant graphs, other constant expressions, mutable signed-64 references,
`!=`, `||`, and overloaded logical operators remain
outside the boundary. Signed integer operands in a Boolean context use the
checked nonzero conversion; they are not truncated to 32 bits first.


Selected or locked dependency headers also admit namespace-scope inline
`constexpr` 64-bit integer constants. Unsigned constants retain a uint64 literal
or a checked uint64 conversion of a signed int32 literal, optionally negated;
the importer independently recomputes the modulo-2^64 conversion and checks
Clang's evaluated value. Thus the pinned `std::dynamic_extent` remains
`18446744073709551615`, without a host-width or low-word substitution. Constant
declarations and initializer spans must belong to the locked source closure;
arbitrary constexpr calls and broader unsigned constant graphs remain refused.

Composed nonthrowing read-only observers can also supply scalar assignment
values. The shared scalar normalizer evaluates the RHS once before changing the
parameter, local, or supported int32 referent. Observer contracts still cannot
write, and each source read still requires caller-held authority.

The `direct-call` fixture selects a caller and captures the transitive closure
of definitions reached by discarded-result direct call statements. Each call
node records the declaration identity resolved by Clang, reference arguments
retain their parameter identity, and all captured functions lower into the
ordinary modular call environment. Each definition has its own sidecar
contract and proof. The artifact rejects recursion, ambiguous reachable names,
and missing definitions. Reachable functions that omit `noexcept` are accepted
only in an exception-enabled normal-only profile (including borrowed trivial records); the baseline profile
continues to reject them. Omitting `noexcept` does not itself declare a Click
exception.

The `return-call` fixtures add direct `return helper(...)` for matching signed
or unsigned 32/64/128-bit and Boolean return types, including concrete function and
method template instances. The typed `return_call` node retains the callee's
Clang identity, typed arguments, result type, source span, and cleanup chain.
Implicit calls on `this` retain the existing checked receiver interface; arbitrary
pointer dispatch remains outside the slice. Lowering captures the result in a
fresh local of its actual type before destroying automatic objects, then returns
that captured value. The synthetic fee wrappers keep Bitcoin's direct method
return-call shape and signed fast-path results; the full upstream wide fallback
is still unsupported.

Regressions prove arbitrary scalar forwarding, branch results, memory framing,
Boolean and wide results before normal cleanup, and object-free normal/exceptional
propagation. Caller proofs agree across verification, expansion/reverification,
and retained audit. Artifact checks reject return-type mismatches, invalid call
graphs, and missing or misordered cleanups. Uncaught return-call cleanup edges
reuse the existing scalar exception lowering and have structural coverage;
resource-bearing exceptional contracts and returns from guarded `try` regions
remain outside the supported surface slice.

A direct free-function return call accepts one nested call argument, including
chains such as `return echo(echo(echo(value)));`. Other arguments must be stable
scalars: literals, locked compiler/constexpr constants, by-value scalar parameters
or scalar locals, and supported integer/Boolean casts of these values. Their
value cannot change across the nested call, and their evaluation is total, so
all C++ argument orders agree. Namespace-scope signed-64 `constexpr` constants
with internal linkage are accepted with or without explicit `static`, under the
existing bounded constant-graph checks. Concrete Boolean template substitutions
also retain their resolved constant value. Field reads and supported casts of
field reads are also admitted when the one nested call has only scalar value
inputs, with no reference/pointer arguments or further input calls. In this
closed profile, mutable globals and external calls are rejected, so such a
callee cannot acquire an alias to the caller's storage. Its field siblings are
checked and captured before the call; their values agree in every argument
order, and a throwing call cannot skip a read's authority check. This covers
`Div(Mul(fee, at_size), size, RoundDown)` with field-backed `fee` and `size`.
General alias analysis is not provided. Reference reads, dereferences,
arithmetic, additional calls, and side effects in sibling arguments fail import.
No unsafe sibling operation can be hidden by selecting an argument order that
skips it. Resource-bearing exceptional contracts remain outside the proof
surface slice.

Each nested result has a checked typed capture; an inner exception skips the
outer call and uses the return's cleanup edge. Verification, selected-caller
expansion/reverification, and retained audit cover all supported scalar types,
argument positions, casts, mixed-width branches, memory writes by the inner
call, normal destruction, and object-free exception propagation. Name allocation
and argument lowering have deterministic scaling coverage. Artifact validation
checks every nested callee, capture type, and sibling storage type and rejects
recursive graphs. Nested calls in integer-local initializers and discarded calls use the same
normalization and ordering checks as return calls. Calls in general value
expressions, converted arguments, and returned references or objects
remain unsupported. Converted integer-local initializers and scalar returns
use the ordered conversion chain described below.

Scalar evaluation is normalized within the C++ frontend into explicit
statements followed by a typed value. Initializer and return artifact wrappers
retain source context; they do not select separate evaluation semantics.
The same ordering policy applies to integer-local initializer, return,
and discarded call arguments. Constructor arguments remain outside nested-call
support. Regressions cover scalar widths/signedness, initializer capture before
cleanup, exception propagation, unsafe siblings in each source position, and
verification/expansion/reverification/audit agreement.

The frontend also prepares contract-facing signatures, Clang layouts, and
local-object metadata alongside kernel execution. C++ and Rust feed the same
prepared execution package to the verifier, using the signature/layout
vocabulary shared with plain C. The shared verifier does not reinterpret C++
artifacts or re-traverse C++ bodies; the original source and locked semantic
identity remain attached to the prepared input.

The synthetic fee fixture preserves `Div(Mul(fee, at_size), divisor, round_down)`
and verifies concrete positive/negative rounding and exact division with
64-bit helpers. It rejects hostile rounding claims, zero divisors, and unproved
product bounds. This does not import upstream Bitcoin fee evaluation: its
`__int128`, `Assume` annotations, and field-reading sibling
arguments still need support.

The `scalar-local` and `signed-arithmetic` fixtures add mutable automatic signed/unsigned
32/64-bit integer locals declared directly
in the function body. An integer local may omit its initializer: declaration
creates uninitialized storage, and a read is refused until execution establishes
initialization. Explicit initialization may use an already-supported integer
expression or a supported direct call. Reference and record locals retain their
initialization requirements. Local
declaration identity comes from Clang; direct-call initialization lowers to the
kernel's ordinary `Declare` and `CallAssign` statements, while later reads and
assignments use the existing scalar rules. This makes call results usable
without treating a compiler-resolved C++ expression as C source text.

Native `unsigned char` values use `uint8` contracts, preserving Clang's
resolved promotions and modulo narrowing conversions. Parameters, returns,
call captures, automatic locals and byte fields share the existing scalar
lowering. Byte fields retain their one-byte layout and independent authority.
Signed/plain character types and `char8_t` remain outside this admission.

Scoped enums with fixed unsigned-char backing also use `uint8` contracts.
Their artifact types retain declaration identity, qualified name, backing type,
scoped/fixed properties and a locked declaration span. Source loads, assignments
and calls require the same nominal type; explicit enum numeric casts preserve
Clang's conversion and use the ordinary native scalar model. An empty fixed
enum still permits all 256 backing values. The actual pinned `std::byte`
declaration has ordinary, expanded and retained offline coverage. Other enum
backings, unscoped enums, named-enumerator references and enum pointers remain
outside this profile. Enum values grant no character alias access; that privilege
is a separate boundary for checked byte pointers.

The `pointer` fixture distinguishes a mutable `int*` parameter from an `int&`
in the Clang artifact. A caller may take the address of its mutable reference
parameter and pass that pointer to a direct call. Pointer lvalue-to-rvalue
conversion, `*pointer` reads, and `*pointer = value` writes lower to the
kernel's existing address, typed-load, and typed-store operations, so the
sidecar must provide ordinary memory authority. Removing that authority or
claiming the wrong pointer-mediated memory effect fails verification.

The bounded native object-pointer profile also admits mutable `unsigned int*`
and `unsigned char*`, using `uint32*` and `uint8*` contracts. Loads, stores,
resolved calls and pointer fields retain their exact pointee type; pointer
arithmetic uses its native element stride. Addresses of automatic `int`,
`unsigned int` and `unsigned char` objects can be formed before initialization,
but reads still require an initialized object. Arbitrary enum pointers do not
acquire character byte-alias permission. Pointer locals, reinterpretation and
other pointee kinds remain outside this slice.

The `struct-member` fixture accepts one named, public, non-inheriting aggregate
`struct` whose fields are mutable `int`, signed 64-bit integers, or mutable `int*`. Clang supplies the
record and field declaration identities plus the exact LP64 size, alignment,
field offsets, and field widths. A function may receive an existing object by
mutable reference and read or write those fields with `object.field`; a pointer
loaded from a field may use the already-supported checked dereference rules.
The proof interface spells that reference as `struct Name*` and uses ordinary
field resources such as `owns state->saved`. Click does not reconstruct the
layout from C++ source or create a synthetic C body.

C++ record returns from live record lvalues admit Clang-resolved trivial copy
construction with trivial destruction and no base subobjects. Sidecars retain
`struct View` result types and `result.field` contracts, including embedded scalar
leaves, through the shared aggregate return model and checked nominal layouts.
Each copied leaf needs initialized read authority. Copying a pointer field does
not transfer ownership of its pointees or grant permission to read them. Copies
complete before automatic cleanup. User-defined copies, moves and named returns
of automatic records remain outside the copy-return slice.

Bounded prvalue construction returns, aggregate-call forwarding and initialization
from such a call use the shared construction mode. The importer recomputes an
eligibility restriction over constructor and helper bodies: their stored values
depend on evaluated by-value arguments and constants, without aliasable memory
reads, storage-address escape or runtime effects. Embedded constructors and pure
helpers satisfy the same restriction. Ordinary checked helper contracts remain
required. This establishes field-value equivalence across C++20's permitted
trivial result copies; a prvalue category alone is not a no-copy guarantee.
Native result types and contracts are unchanged, and incomplete construction is
refused. Address-sensitive returned constructors, nontrivial destruction, NRVO
and mixed copy/construction return branches remain outside this profile.

Returned-constructor arguments also admit composed nonthrowing expression
observers when every argument is a value expression. The existing observer
contract check requires read-only effects, and the shared scalar normalizer
evaluates each call once before construction. Mixing these expressions with
ordinary nested calls or reference arguments remains refused. Constructor-body
eligibility still applies independently to the already evaluated arguments.

Assignment from an admitted construction-return call requires Clang-resolved
trivial copy assignment and an exact nominal RHS temporary lasting for the full
expression. Click constructs into distinct raw RHS storage, copies into the live
LHS and retires the RHS. References into separate backing remain usable only
under the caller's existing authority. Move assignment, user-defined assignment
and other materialization shapes remain refused. Artifact schema 57 requires an
explicit refresh of earlier locks.

Taking the address of a supported int32 record field uses its checked Clang
projection and the shared storage-lifetime checks. It preserves const
qualification inherited from the root object and does not read the field or
grant permission to dereference the resulting pointer. Constructor initializers
can therefore store a pointer to a field of the destination object. This differs
from copying an existing descriptor, which preserves pointer values rather than
rebasing them to a new object. Artifact schema 57 requires refreshing earlier
locks. Returned constructors use the narrower eligibility restriction above.

Native int32 reference results and locals can also bind supported record fields
through that same checked field-address path. Const qualification is preserved;
a returned alias grants no backing authority. An external backing reference
can remain readable and writable after a descriptor's destructor clears its
pointer field, when the caller retains the corresponding backing authority.
A reference into a destroyed automatic object's own field cannot be read.

Literal `nullptr` and integer zero converted to mutable native `int*`,
`unsigned int*` or `unsigned char*`, implicitly or
through an explicit cast, lower to the shared C null pointer value. Returning
or storing that value needs no pointee authority and grants none. Dereferencing
it remains subject to the shared live-storage and access checks. Same-type
explicit pointer casts preserve identity. Other pointee types, nonliteral
`nullptr_t` expressions, and nonzero integer-to-pointer casts remain refused.
These nodes use artifact schema 57; refresh earlier locks.

Mutable pointers to the pinned libstdc++ `std::byte` declaration also use native
`uint8*` contracts, with one-byte loads, stores, offsets and field layout.
The importer checks the enum identity and declaration span against the locked
libstdc++ header hash, including offline artifacts. Other enums retain their
native scalar values but do not gain byte pointer or alias permission. The
current standard-byte profile is limited to that pinned header; other standard
library versions require a separately checked declaration pin. Taking an
uninitialized automatic byte object's address does not read or initialize it;
a checked store does. Initialized mutable native pointer locals retain their
pointee types through direct values, captured calls and same-type assignment.
Their initializer remains mandatory.

Explicit `reinterpret_cast` to the authenticated `std::byte*` is admitted from
mutable native int32, uint32 and unsigned-byte pointers. It changes the access
type and byte stride without granting ownership or initialization, and retains
an explicit artifact node or call-result conversion. Reverse typed casts,
nonstandard enum targets, const removal and general character-pointer
reinterpretation remain refused. Concrete byte stores use the shared byte
representation rules; on the selected target, four checked stores can initialize
an unwritten declared uint32, while partial stores cannot. Native contract
casts such as `result == (uint8*)p` express pointer identity across access
types without granting authority. Dynamic-extent `std::span<std::byte>` now
retains authenticated standard-byte template arguments, including their
positions and locked declaration metadata even when fields do not mention
the enum. Other enum template arguments remain refused. A class template
also takes `unsigned char` as a type argument, as in `std::span<unsigned char>`;
integral template values remain 32/64-bit. The catalog contract
for `std::as_writable_bytes(std::span<int>)` preserves the backing address and
returns four times the native element count, without granting backing authority.
Supported `const` and `constexpr` native integer locals now use shared scalar
construction: allocate, initialize once, and freeze the object while retaining
its address and lifetime. Ordinary assignment and alias writes cannot mutate
read-only storage. Helper-result initializers use checked mutable captures and
then initialize the distinct source object. Schema 59 requires refreshing older
locks. Const aggregate/array locals and general constant evaluation remain
outside this bounded slice.


Static scalar methods use a distinct `static_method` artifact kind with their
class and declaration identities, without an implicit receiver or object-layout
requirement. Select an ordinary declaration with `Class::helper`; reachable
concrete function-template instances retain their existing distinct names.
Class-qualified and unqualified calls support the existing scalar initializer
and return-call positions, including one nested call with stable scalar siblings.
Parameters and results must be supported by-value integer or Boolean scalars.
Object-qualified static calls are rejected, including calls whose receiver has
side effects. Virtual dispatch and reference/pointer helper signatures remain
outside this slice. An unrelated unsupported field does not block a static
helper that never accesses object storage.

The synthetic `static-helpers.cpp` fixture preserves static `Mul`, `Div`, and
Boolean template forwarding, with positive and negative rounding proofs.
Selected-caller verification, expansion/reverification, and retained audit
agree. Regressions cover every scalar type, distinct classes, initializer calls,
scalar exception propagation, false claims, and malformed artifact identities
and signatures. This removes the static-helper prerequisite; Bitcoin's wide
arithmetic, checked `Assume`, and field-reading sibling arguments remain open.

The `value-methods` fixtures add non-static, non-virtual ordinary methods on
that record. Select a method with `"function": "FeeFrac::IsEmpty"` or
`"function": "FeeFrac::operator+="` (or `operator-=`). The proof interface names
them `FeeFrac_IsEmpty`, `FeeFrac_operator_add_assign`, and
`FeeFrac_operator_subtract_assign`, with an explicit first
parameter `this`. Const methods use `const struct FeeFrac* this`; const record
reference parameters retain the same qualification. This restricts writes
through that parameter without forbidding an alias through a mutable parameter.
Direct nonvirtual `operator[]` methods also use this method-call path, with
`Class::operator[]` as the selector and `Class_operator_index` as the proof
name. The receiver must be a live record lvalue; argument and result types,
const qualification and reference authority follow the ordinary method rules.
This does not admit other overloaded operators or temporary receivers.

Unused member functions, constructors, templates, and nested declarations are
not imported into the execution graph. Reachable definitions and the record's
complete supported field layout are still checked. Overloaded proof names and
reachable unsupported bodies fail import.

Direct `object.method(...)`, explicit `operator+=`/`operator-=`, and
`object += other`/`object -= other` calls bind that receiver to the selected declaration identity. Call arguments
must be direct supported references or the existing value arguments; pointer
receivers, virtual dispatch, other overloaded operators, and call results
outside the scalar-local initializer and direct scalar return-call slices remain unsupported.
Same-width signed field `+=` and `-=` use checked loads, arithmetic, and
stores. Compound updates with side effects or mixed-width conversions remain
unsupported. Overflow obligations apply to each field's
width. The fixtures prove disjoint-object addition, self-addition with one set
of field resources, and preservation of unrelated caller memory; they reject
false claims and missing authority or overflow bounds.

The [Bitcoin Core integration](https://github.com/clicklang/click/blob/master/integrations/bitcoin-core-money-range/README.md#fee-frac-value-methods)
verifies these same properties for unchanged upstream `FeeFrac` methods under
the real project profile. This does not prove the class's other methods or
its documented application invariant. The typed artifact schema is now 42;
previous artifacts require an explicit lock refresh.

The offline checker validates recursive function metadata before checking the
supported semantic profile. It checks source spans, declaration metadata, and
type-alias provenance and cycles throughout both branch arms, scopes, handlers,
initializers, calls, and cleanup lists. A malformed node inside an unsupported
lifetime arrangement reports a metadata error first. Supported widths, operand
types, lexical visibility, and cleanup ordering are checked separately; valid
metadata alone does not make a construct supported.

Artifact resource limits are independent of the supported C++ semantic profile:

| Budget | Limit |
| --- | ---: |
| Record declarations | 256 |
| Constant declarations | 1,024 |
| Function declarations, including the selected root | 1,024 |
| Call graph depth, including the selected root | 64 |
| Local declarations per function, including catch bindings | 1,024 |
| Cleanup scopes per function | 256 |
| Serialized JSON object/array nesting | 96 |
| Serialized JSON objects and arrays | 65,536 |
| Preprocessor files | 4,096 |

Exhaustion names the budget. Serialized bounds are checked before decoding;
the pinned exporter also bounds declaration discovery. Structural checks still
reject duplicate IDs, missing or mismatched references, invalid layouts, and
declarations outside the selected graph. Recursive calls remain unsupported
semantics. Acyclic constant forests may have multiple leaves and longer chains;
each initializer retains the supported literal-leaf or literal-times-prior-constant
form, and the checker independently recomputes every evaluated value. Multiple
record layouts reuse the existing field-type, explicit ABI, and ownership rules.
Local and scope budgets count both branch arms; parameters do not count as
local declarations. The exporter and checker enforce these counts independently.
Lifetime combination restrictions described below remain semantic-profile rules.

C++ graph validation indexes each function's parameter, local, and catch-binding
identities once. Reference arguments and destructor edges use borrowed type
lookups. Reusing a declaration ID anywhere in the function is rejected, including
across sibling scopes. Equal local names in disjoint scopes remain distinct
when their declaration IDs differ. Separate lexical and lifetime validation
checks visibility, construction, and cleanup order.

C++ calls and contracts bind through Clang declaration IDs. Unique readable
names are preserved; free namespace names replace `::` with `_`. If reachable
declarations share a readable name, each contract name is `__click_cpp_decl_`
plus the full lowercase hexadecimal UTF-8 declaration ID from the artifact.
This prefix is reserved: source declarations beginning with it also receive
encoded names, as do spellings that are not valid sidecar identifiers
(such as anonymous namespace members). The lowered-import API exposes
`contract_name(declaration_id)`.
Reachable overloads are supported; selecting an overloaded declaration directly
still fails until a signature selector is available.

A direct statement `__builtin_assume(condition)` creates a checked proof
obligation at its source location. The condition must be proved from contracts
or preceding control flow; the importer never inserts it as a trusted fact.
Lowering uses the common kernel's labeled assertion operation. A missing or
false condition fails verification even when the function's result claim would
otherwise hold. Normal returns and destructor cleanup remain unchanged.

Clang identifies the intrinsic by builtin declaration identity. An ordinary
function named `Assume` has ordinary call semantics. The builtin does not
evaluate its operand, so this slice accepts only total predicates over by-value
scalar parameters/locals and locked constants: supported casts, comparisons,
and logical conjunction. Reference/pointer/field reads, runtime calls, arithmetic,
and side effects are rejected. Compiler-folded constants retain the existing
pinned-Clang constant policy. Bitcoin's library `Assume` macro and general
assertion/abort behavior remain unsupported. Schema 37 requires an explicit
refresh of earlier locks.

Scalar interpretation is shared by the artifact validator, execution lowering,
and proof-facing signatures. It distinguishes mutable and const qualification
from the seven supported value kinds: Boolean, int32, int64, uint32, uint64,
int128, and uint128.
Integer literals use one checked parser in validation and lowering. Source
aliases preserve provenance without changing the value kind. Reference and
record-field restrictions remain specific to their positions in the profile.
Explicit integral casts use one C++ conversion policy over the common kernel;
the frontend does not re-infer promotions from source syntax.

The `signed-arithmetic` fixture lowers signed 32/64-bit `+`, `-`, `*`, `/`,
`%`, unary negation, and `==`, `!=`, `<`, `>`, `<=`, `>=` into the common checked
kernel. Clang's integral promotions and signed casts are explicit artifact
nodes; mixed-width operands require those conversions. Signed 64-to-32
narrowing follows C++20's modulo semantics using the kernel's unsigned bit
conversion and signed reinterpretation. Boolean conversion preserves the
nonzero meaning of all 64 bits. Division truncates towards zero, and remainder
has the dividend's sign. Zero divisors and the `MIN / -1` and `MIN % -1`
overflow pair fail verification. Addition, subtraction, multiplication, and
negation retain their signed-overflow obligations. Scalar local call initializers
also accept an ordered chain of Clang-resolved integral and Boolean conversions,
including explicit same-type alias casts. Each conversion retains its exact
cast kind, explicit/implicit origin, source and result types, alias provenance,
and executable source span. The shared scalar normalizer calls the helper once
into a temporary of its original return type, then converts that captured value
into the declared local. Direct matching-type calls keep their existing lowering.
C++20 narrowing uses the same modulo policy as pure casts; it does not establish
a mathematical result-fit claim or remove overflow obligations in the callee.
Modular contracts, memory authority and exception cleanup still apply.

Scalar returns use the same conversion-chain exporter, metadata validator and
normalizer. This admits implicit return widening and explicit integral/Boolean
casts around a whole direct call, including same-type alias wrappers. Callee
contracts keep the original return type; the return node records the final
converted type, and graph validation checks both ends of the chain. Lowering
evaluates the call once, converts its capture, then captures the converted
result before any active destructor runs. Throwing calls use the existing
exception cleanup edge. Normal and scalar exceptional contracts have offline
ordinary/expanded/retained proof coverage; resource-bearing exceptional
contracts remain outside the proof surface.

Both contexts bound a chain to 256 Clang conversion steps in the exporter and
artifact validator, so a flat artifact cannot build unbounded nested kernel
casts. Converted arguments, arithmetic around calls and call-based brace
initializers remain outside this slice. Original 128-bit callee results retain their typed capture through conversion.
For a value-preserving narrowing proof, name the captured result, transport both
destination bounds from its modular contract, and apply the existing checked
cast certificate to that value. This also checks initializer and return proofs
offline; no automatic observer normalization or range inference is implied.
Schema 45 requires refreshing earlier locks.

The pinned unchanged Bitcoin `CFeeRate::GetFeePerK` separately composes the
unified Down contract at 1000 bytes, with positive size and explicit result fit.
It has no empty-rate branch or minimum correction.

The pinned unchanged Bitcoin `CFeeRate::GetFee` integration composes the
read-only `IsEmpty` contract and the unified Up result-fit contract through
these calls and conversions. It proves zero for an empty rate without fee or
fit premises, ceiling rounding on the nonempty profile, the negative minimum
correction, int64 result bounds and both field frames. See the
[integration proof and explicit assumptions](https://github.com/clicklang/click/blob/master/integrations/bitcoin-core-money-range/README.md#getfee-composition).

The fixture preserves Bitcoin's quotient/remainder correction expression with
a signed 64-bit dividend. It checks both rounding directions for positive and
negative dividends, exact division, zero, signed extrema, and the largest
positive int32 divisor, together with expansion and retained audit sessions.
These are concrete rounding cases, not a general rounding theorem. General
quotient/remainder contracts and a modular caller with unrelated memory also
verify. Bitcoin's actual rounding helper still requires the remaining wide rounding
operations and conversion bounds described below.

The `wide-intermediates` fixture admits signed and unsigned `__int128` locals,
compiler constants, and Clang-resolved integral casts inside functions with the
existing 32/64-bit or Boolean signatures. C++20 casts use the shared modulo
conversion policy, and Boolean conversion observes all 128 bits. Signed wide
multiplication uses the shared checked runtime operation; casting a narrow
product afterwards cannot remove its original overflow obligation. High-bit
products, signed extrema, symbolic cast round trips, source-width overflow,
wide overflow, expansion, and retained audit have regression coverage.

The `scalar-braces` fixture admits one Clang-resolved integer or Boolean
brace initializer, including `__int128{a}` and `long value{n}`. It preserves
the semantic child's resolved conversion through the existing expression
model, including argument stability and compiler-assumption checks. C++
narrowing list initialization remains a compiler error; empty lists,
unsupported scalar widths, and unsupported effects remain refused. This
normalization adds no artifact node or schema version.

On a normal wide multiplication path, after both native range guards hold,
the shared kernel certifies the result's mathematical observation as the
exact Integer product. Pure Integer observation and capture retain the native
guards but do not demand that a certified result definition be supplied as
another assumption. False product claims and missing guards remain refused.

The `wide-contracts` fixture adds by-value wide parameters, results, and
matching-width call captures. Contracts spell these types `int128` and
`uint128`; `to_integer(value)` observes their full mathematical value.
`to_int128(z)` and `to_uint128(z)` require both exact destination bounds;
these proof conversions remain distinct from C++ modulo casts. Identities,
cast round trips, full signed/unsigned endpoints, modular calls with framed
narrow memory, expansion, and retained audit have regression coverage.
Bounded `simp` recognizes direct observer equalities; it does not currently
chain two Integer observer equalities through nested calls.

The `wide-division` fixture adds signed and unsigned 128-bit `/` and `%`.
Clang-resolved promotions remain explicit, including modulo conversion of a
negative narrow operand to unsigned 128 bits. Division truncates toward zero;
a nonzero remainder has the dividend's sign. Both operations require a nonzero
divisor. Signed operations additionally exclude `MIN / -1` and `MIN % -1`.
Contracts use `truncating_quotient(to_integer(a), to_integer(b))` or
`truncating_remainder(to_integer(a), to_integer(b))` for exact full-width
results. A signed contract can state the overflow exclusion as
`to_integer(a) != MIN or to_integer(b) != -1`, with the full Integer literal
for MIN. Missing guards and false results are refused, including for trivial
postconditions. Symbolic contracts, constants above 64 bits, modular caller
framing, offline verification, expansion, and retained audit have coverage.

The `wide-comparisons` fixture adds all six comparisons (`==`, `!=`, `<`,
`<=`, `>`, `>=`) on signed and unsigned 128-bit values. Comparison uses the
full mathematical observation with the operand's signedness; Clang-resolved
promotions remain explicit. The shared native and pure-spec condition
constructor keeps execution and retained branch proofs consistent. Boolean
contracts describe results as `0` or `1` and relate them to comparisons of
`to_integer(a)` and `to_integer(b)`. Exact premises and their complementary
relations settle known results without scanning unrelated proof facts.
Symbolic results, high-bit constants, mixed-width promotions, branches,
modular caller framing, offline verification, expansion, and retained audit
have regression coverage. Undefined operand arithmetic still fails even with
a trivial postcondition. `!=` is also admitted for the existing 32/64-bit
scalar profile.

The `wide-narrowing` fixture proves when existing C++ modulo casts preserve
full mathematical values. The explicit `integer_cast_identity` `rules`
arithmetic certificate consumes two named constant-endpoint bounds on the
source observation, checking both against the destination range. Both signed
and unsigned 128-bit values narrow to signed/unsigned 32/64-bit results.
The rule also checks native quotient/remainder narrowing under their existing
definedness guards and stated result bounds. Out-of-range casts still wrap;
missing range premises, false results, and undefined operands are refused.
Modular caller framing, offline loading, expansion, and retained audit have
coverage. This adds proof support without changing the schema or trusting
conversion bounds. See [Integer certificates](../../internals/mathematical-integers.md#range-checked-modulo-cast-identities).

Operand intervals can now supply the quotient/remainder narrowing bounds through
an explicit `integer_division_bounds` certificate. The separate
`integer_relation_transport` certificate moves those mathematical bounds along
the exact native observation equality, then composes the range-checked cast
identity with that observation. These are shared proof rules with no automatic
range inference or change to the C++ source model. The narrowing regression uses
full signed 64-bit numerator observer bounds and a positive signed 32-bit divisor
range, states the native guards separately, and checks verification,
expansion/reverification, retained audit, and false result claims.

Wide pointers, references, record fields, arrays, negation,
addition, subtraction, and unsigned multiplication remain unsupported. Both
the live exporter and serialized artifact validator reject these operations.
Schema 40 requires refreshing older locks. The unchanged Bitcoin fee
division helper still needs quotient/remainder and narrowing bounds plus an
explicit treatment of the library `Assume` boundary. The unchanged
`FeeFrac::Mul` now has an exact product proof under explicit full-width
operand observer bounds in the
[Bitcoin integration](https://github.com/clicklang/click/blob/master/integrations/bitcoin-core-money-range/README.md#wide-fee-product).

Unsigned 32/64-bit scalar parameters, returns, locals, direct captures, and
same-type arithmetic/comparisons now use the common unsigned kernel types.
Addition, subtraction, multiplication and negation wrap modulo the width;
division and remainder require a nonzero divisor. Clang exports the usual
arithmetic conversions explicitly, so mixed signed/unsigned source expressions
retain their C++ meaning. Signed-to-unsigned conversion is modulo the target
width; unsigned-to-int32 narrowing reinterprets the low 32 bits. Uint32-to-int64
is an exact widening. C++20 uint64-to-int64 conversion preserves all 64 bits:
values through `INT64_MAX` retain their value, and higher values denote the
congruent signed value modulo 2^64. The importer selects the explicit kernel
`UInt64BitsToInt64` cast mode; ordinary C casts retain their existing checks and
supported slice. Subsequent signed operations retain overflow obligations.
Unsigned references and record fields, runtime narrow/wide integer types,
bitwise operations, and general templates remain outside this slice.

The `unsigned-arithmetic` fixtures check wraparound, extrema, casts, modular
caller framing, division guards, and both unsigned fee fast-path expressions.
Those fast-path cases return the unsigned intermediate and do not prove
upstream `EvaluateFee`. The kernel strengthens unsigned constant bounds using
only the queried endpoint's index, including negated bounds and values above
the signed sign bit; deterministic regressions grow unrelated fact populations.

The `signed-conversion` fixtures verify explicit and implicit conversions at
the sign bit and both extrema, both round trips for arbitrary inputs, a modular
bit-preservation contract with unrelated memory, and subsequent signed overflow.
They preserve the instantiated fee fast-path expressions and signed return type
and verify concrete rounding/boundary cases. The complete upstream `EvaluateFee`
implementation and a general rounding theorem remain open. Conversion proofs
agree across ordinary verification, expansion/reverification, and retained audit;
false signed results are rejected. The shared bitvector representation preserves
source bits and uses typed signed operators for subsequent computation. Indexed
bit-preserving equality rules have fact-population and expression-depth scaling
regressions.

The pinned Clang exporter evaluates constant `sizeof` expressions and static
zero-argument constexpr `std::numeric_limits::max()` calls in selected expression
positions. These produce distinct `compiler_constant` nodes with a checked
32/64/128-bit value/type and the original source span. The exporter preserves runtime
expression semantics under the pinned target and locked preprocessor input
closure. Standard-library semantics remain part of the trusted compiler input.
Runtime calls are never folded by this allowlist. General constexpr calls in
runtime expression positions, unsigned namespace constants, and local
call-capture initializer forms outside the ordinary call slice remain unsupported. The unchanged Bitcoin `GetSizeOfCompactSize` proof covers every
uint64 input in four disjoint ranges, checks expansion and retained audit, and
rejects false encoded-length claims. It proves encoded length, not serialized
bytes or a round trip.

Concrete function-template instances are supported when reached through an
ordinary selected caller and their instantiated operations fit the existing
profile. Boolean value arguments and unqualified builtin `bool`, `int`,
`unsigned int`, `long`, `unsigned long`, `long long`, and `unsigned long long`
type arguments are accepted. Each instance keeps its distinct Clang USR.
Sidecar names append argument tokens in order, such as `choose__bool_true`,
`identity__unsigned_long`, or `Value_select__bool_false`. Type aliases use the
canonical builtin token; equal-width types such as `long` and `long long`
retain different names. Callable name collisions use the existing injective
Clang-declaration identity names.

Concrete class-template instances reached through ordinary selected callers
use the same ordered builtin/Boolean argument tokens, plus `__tag_Name` for
named empty trivial tag types declared in the locked import root. For example, `Box<int, false>` exports as `Box__int__bool_false`,
while `Box<SizeTag, true>` exports as `Box__tag_SizeTag__bool_true`.
Qualified tag names include their namespace components. Clang's canonical USR
keeps each record, field and method nominally distinct even when layouts match;
aliases share the canonical instance. Method, constructor and destructor names
use the concrete record name. Record-name collisions are import errors. At most
32 class arguments are supported. Clang completes reachable specializations
before layout export, including unused reference parameter types; incomplete
record declarations fail import without an artifact. Instances must satisfy
the ordinary record and executable-body profile, including the bounded single-base layout profile below, supported fields and
destruction, and no virtual dispatch. Empty tags serve only as type arguments;
this does not add empty runtime objects. Click verifies the
resolved layout and bodies without performing template substitution itself.

A `do { ... } while (false)` or `do { ... } while (0)` wrapper executes its checked body
once through the shared conditional model. Only literal false conditions are
admitted; runtime/repeated loops, break/continue and nested automatic locals
remain refused. This admits the wrapper shape used by assertion macros without
assuming their bodies or conditions.

Return values and ordinary `if` conditions may contain direct, nonthrowing
scalar observer calls inside supported arithmetic, comparisons, pointer offsets
and reference-address formation. The normal-only profile requires every such
callee, including nested argument calls, to verify with `views` permissions
only. Ownership transfer and resource construction are refused. A final
unchanged-value claim alone does not qualify an observer: writes followed by
restoration still fail under views. Native `const` is not a substitute for this
proof.

These calls reuse the scalar-call normalizer and modular contracts. Read-only
permissions establish that unsequenced operands cannot interfere; short-circuit
`&&` places the right operand's call prefix inside the conditional branch, so
an unevaluated operand needs no read permission. Assignment, local initialization,
constructor arguments and other expression-call contexts remain unsupported.
Ordinary, expanded and retained proofs cover symbolic field reads, nested
arguments, signed widening and short-circuit permissions; false claims, writes,
owning contracts and forged call identities/types/spans are refused.

Integral logical negation also uses shared C truth conversion and returns a
native Boolean, including full-width unsigned values and observer results.
In selected runtime function bodies, `__builtin_is_constant_evaluated()`
returns false. Clang still selects manifestly constant `if constexpr` branches;
this operation does not replace compile-time evaluation. Supported read-only
scalar locals retain initialized storage, but their initializers cannot observe
constant-evaluation context directly or through reachable callees. This checked
boundary prevents a runtime `false` from standing in for a constant evaluation;
unrelated runtime observers remain supported.
`__builtin_unreachable()` becomes a checked false assertion: its execution
path must be proved unreachable.

Macros from declared dependency headers retain their locked definitions and
use Clang's expansion locations within the executable function. Missing macro
dependencies are refused, and changing a definition invalidates the offline
artifact. Reference typedefs compare their resolved pointee types, retaining
width and const qualification. Function-directed proof expansion prints a
reference result's address as `&result` and its referent as `result`.

An ordinary `if` can use a direct Boolean free-function or method call as its
whole condition. The artifact keeps this effectful call separate from pure
expressions. The shared scalar-call normalizer evaluates its bounded arguments
and captures its result once before branching; callee contracts preserve memory
authority and sibling frames. Supported inherited receivers and the existing
single nested, order-independent scalar argument profile also apply. Calls
propagate scalar-int32 exceptional outcomes and unwind active objects under the
existing lifetime restrictions. The conditional guarded-try shape remains
pure-only because its lowering moves the condition outside the catch.
Compositions such as `!call()`, `call() && other`,
comparisons of call results and integer-to-Boolean call conversions remain
unsupported. Reachable ordinary method/free-function definitions can come from explicitly
locked dependencies as well as the selected file. The selected function stays
in its configured logical source. Each reachable function owns one source:
parameters, statements, expressions, call sites and projected uses must stay
within it, while type-alias declarations may come from any locked declaration
source. Every reachable body outside a system header is exported, validated
and verified through its ordinary sidecar contract. The bounded nonthrowing constructor profile also
admits locked headers. Dependency-header destructors, constant definitions and
executable spans crossing source files remain unsupported.

For `if constexpr`, pinned Clang chooses the instantiated arm in constant
evaluation context. The artifact retains an ordinary constant Boolean `if`,
the selected arm, an empty discarded arm, and the original statement and
condition spans. The condition uses a distinct `compiler_constant` under a
Boolean conversion. Discarded code contributes no runtime calls, accesses,
or cleanup. A selected unsupported arm fails import. Ordinary `if` statements
continue to import both arms. Return validation checks the reachable arm of a
closed constant Boolean condition and both arms of an unknown condition.
Empty statements and successful nondependent `static_assert` declarations
contribute no runtime operations. Pinned Clang checks the assertions, and their
source remains in the locked import closure; dependent or failed assertions
are never discarded by this rule.

The `template-instances` fixture checks modular callers, receiver authority,
framing, false contracts, same-width type identities, Boolean substitution,
constant-evaluation context, and unsupported arguments. Its instantiated fee
fast paths retain the unsigned expressions and cover both rounding directions
with expansion/reverification and retained audit. They remain synthetic
prerequisite proofs, not verification of upstream `EvaluateFee`. Selecting a
dependent template pattern, packs, other non-type arguments, qualified type
arguments, non-scalar function-template arguments, nontrivial class tag types,
and calls in unsupported expression positions remain outside this slice. Template substitution and constexpr
selection are trusted compiler operations under the locked input profile;
selected function implementations still require verified sidecar contracts.

The shared signed-64 reasoning rules also verify `x + z` and `x - z` across
the full signed range when a modular helper establishes `z == 0`. They retain
the equality's proof provenance, read only the queried operands' fact indexes,
and strip chains of zero additions through borrowed operands. Deterministic
regressions check unrelated fact populations and increasing expression depth;
the C `int64_returned_zero_identity` fixture covers the common kernel path.

Named standard-layout structs and classes may include private or protected
fields; Clang checks source access control, while sidecar views and ownership
provide memory authority. Reachable record and field declarations may originate
in explicitly locked project headers. Their spans retain that header's identity;
each function body and its field-use spans belong to that function's definition source.

Embedded mutable records with trivial destruction retain nominal child
identities and exact ABI extents, offsets and alignment. Contracts can describe
nested fields using C's existing struct metadata, as the `nested-record` fixture
shows when an outer scalar update preserves fields in two separate child
objects. Declaration validation follows embedded-field reachability and rejects
by-value cycles without expanding shared layouts. Physical leaf layouts used
by contract preparation have a 65,536-leaf budget across the import. Nested
source field reads, writes and signed compound updates retain ordered
owner/field declaration paths from the root object. Validation and lowering
share an indexed resolver and exact accumulated byte offsets. Root constness
applies to the full path; ownership and views apply to the accessed leaf, with
separate sibling objects retaining separate authority. A const object's pointer
field may still reference mutable memory; pointee authority is checked separately.
Projection use spans belong to their enclosing function's source. Methods and helpers can
receive an embedded record by reference, and helpers can receive a signed-32
field by reference. These calls use the same checked field path and exact byte
address. The root's constness controls binding to mutable references, including
implicit method receivers; it cannot be discarded by projecting a mutable field.
Callee contracts require authority at the selected subobject or scalar leaf and
preserve sibling frames. Plain scalar locals, temporary objects, arbitrary record
pointers and inherited subobjects remain outside this reference-call slice.
Automatic embedded construction uses the constructor profile below.

The `local-aggregate` fixture declares one automatic object of that same record
kind directly in a function body. It must use direct braces with exactly one
initializer for every field in declaration order. The artifact binds those
expressions to Clang field identities, and direct lowering allocates the exact
Clang layout as kernel stack memory before applying typed field stores. Later
`object.field` reads use the same checked offsets as an existing object passed
by reference; trivial scope exit needs no destructor action.

The `constructor-local` fixture permits that one automatic object to use one
public, non-default `noexcept` constructor. The selected constructor may be
explicit, non-explicit, or conditionally explicit: Clang has already resolved
the direct invocation. Its member-initializer
list must initialize every field in declaration order; the constructor body
and its implicit call at the declaration are both lowered and verified through
the ordinary modular call rules. Embedded record fields with trivial destruction
can use their own resolved constructors in that same ordered initializer prefix.
Each child call uses its exact field address and native contract; it neither
resizes the parent allocation nor initializes siblings. Repeated initialization
outside the prefix, mismatched nominal constructor targets, base construction,
and nontrivial embedded destruction remain refused. Constructor proof entries
describe unwritten object footprints without fixing their containing allocation's
extent. Ordinary, expanded and retained checks cover an automatic descriptor
with a pointer field and a nested uint64 extent while preserving backing memory.
A nested self-pointer regression also constructs a child at a nonzero parent
offset and reads through the pointer to that child's own field.

Constructor bodies may come from declared, locked header dependencies. Scalar
member initializers can call nonthrowing observers through their checked
read-only contracts; lowering captures the call result before storing the
field. Exception-enabled normal-only imports permit these local objects when
destruction is trivial. Throwing construction, header destructor bodies, and
nested calls in constructor arguments remain outside this slice.

The `terminal-destructor` fixture adds one public, non-virtual, non-deleted,
explicitly `noexcept` destructor with a nonempty supported body. The artifact
records its declaration identity on the record and records its implicit call
as cleanup on the function's single final return. Direct lowering first
captures the return expression in an internal scalar local, then calls the
checked destructor, then returns the captured value. The fixture proves that
the destructor restores caller memory while the result retains the value seen
before cleanup; missing and false destructor contracts are rejected.

Lifetime planning derives each destructor from the typed local and record
identity, independently of the artifact's cleanup lists. A scoped construction
stack supplies cleanup for returns, lexical fallthrough, and exceptional exits;
validation checks that exported lists match the live objects in reverse order.
An initializer's exceptional continuation never activates its destination.
Catch boundaries delimit unwinding, while returning captures the result before
destruction. This replaces arrangement-specific lowering and final-return-based
destructor discovery. Constructors remain nonthrowing in this profile; partial
construction, temporaries, copy/move, and wider exceptions remain unsupported.

The `early-return-destructor` fixture permits structured `if` statements after
one destructible object has been constructed directly in the function body.
Every return edge captures its result and then invokes that same checked
destructor. It verifies the original two-path `Restore` example: the early path
returns 7, the final path returns 9, and both restore the referenced integer to
its entry value. Returns before construction carry no cleanup for the future
object. The `construction_prefix` fixture also returns between two constructions;
each return destroys only its successfully constructed prefix.
The `examples/basic-cpp/` project also selects a modular caller starting with
41: either captured result is retained while the referenced cell is 41 after
the call.

Multiple top-level objects are supported when all require destruction and use
the supported constructor and destructor, within the local declaration budget.
The `reverse-destructor-order` fixture demonstrates two objects. Both objects
are activated individually after successful initialization. A return after both
constructions records the second object's
destructor before the first object's destructor, and lowering checks those
calls in that order. The fixture makes the ordering observable: the second
guard restores 7 before the first guard restores the caller's entry value.

The `nested-scope-destructor` fixture alternatively permits one explicit block
directly in a free-function body. Such a block may contain multiple directly
constructed destructible objects, within the declaration budget, and no other
block locals. The fixture demonstrates one object. A return from the block captures
its value before running the destructor, while normal fallthrough runs the
same checked cleanup before the next outer statement. The artifact retains
that lexical boundary as a `scope` statement; the outer return consequently
has no cleanup for the already-destroyed object.

Sibling blocks are supported within the cleanup-scope and declaration budgets
when their object lifetimes do not overlap. The `sibling-scope-destructors`
fixture demonstrates two such blocks. Each sibling carries its own return and
fallthrough cleanup, and the next block begins only after the preceding
destructor. The fixture deliberately reuses the source name `guard`; distinct
Clang declaration identities and the kernel's sequential local-lifetime rule
keep those objects separate.

The `overlapping-scope-destructors` fixture instead composes exactly one outer
destructible object with exactly one inner cleanup scope. A return from the
inner scope records the inner destructor before the outer destructor. Normal
fallthrough destroys only the inner object, and the final function return then
destroys the still-live outer object. The proof makes the order observable by
checking that both paths return the value restored by the inner guard while the
outer guard ultimately restores caller memory. Conditional construction,
deeper blocks, shadowing between the two live objects, a second inner scope,
and broader overlapping lifetimes remain rejected.

The `conditional-construction` fixture permits exactly one top-level `if` to
contain one cleanup scope in one otherwise-empty arm. The object's constructor
and destructor occur only on that arm: an early return destroys the object,
normal arm fallthrough destroys it before the outer continuation, and the
skipped arm plus final return carry no cleanup. The destructor contract has a
precondition established by construction, so verification would reject a
destructor synthesized on the path where no object exists. Objects in both
arms, combination with another aggregate or cleanup scope, and deeper
conditional construction remain rejected.

A record may have one public, non-virtual base when it has no fields of its
own, remains standard-layout and trivially copyable/destructible, and preserves
the complete base's size and alignment at offset zero. The artifact stores an
explicit nominal `base` edge with its own layout and source span; inherited
fields are not copied into the derived declaration. The base must itself belong
to the locked, reachable record graph. The proof interface exposes its storage
under `base`, for example `state->left.base.fee`, retaining ordinary field
authority and sibling frames. Base chains use the bounded record-layout walk
and leaf-materialization budget. Forged edges, layouts and cycles are rejected.
Inherited field reads/writes and method calls, and implicit derived-to-base
record-reference arguments, use ordered paths that may mix fields and bases.
Each base projection records its derived owner, nominal base target and use
span in a distinct `base` wrapper; ordinary field projections retain their
existing encoding. Validation checks each declared edge and the final field or
callee identity, and lowering uses the accumulated byte offset. Constness
propagates from the complete root object across both kinds of edge. Clang still
checks source access control. Offline ordinary, expanded and retained proofs
cover base chains, mixed-width leaves, const/mutable calls and sibling frames;
recomputed artifacts reject wrong nominal targets even with equal layouts,
reordered/incomplete paths, forged spans and mutable binding through const roots.
Explicit casts, automatic derived objects and base constructor/destructor
execution remain unsupported. Multiple or virtual bases, empty bases, own
derived fields and tail-padding reuse remain outside this profile.

Discarded-result trivial copy assignment between live lvalues of the same
nominal record lowers to shared C aggregate field copies. Clang must resolve a
non-deleted, non-virtual trivial copy assignment; the record and embedded
records require trivial destruction and no base subobjects. Const sources and
nested record projections are supported. The destination requires write
authority and the source requires read authority for every scalar leaf. Checked
Clang layouts preserve native pointer and unsigned extent values; copying a
descriptor transfers no backing-storage authority. Self-assignment preserves
the fields. User-defined assignment bodies and move assignment remain refused.

Copy construction and moves, default or partial aggregate initialization, multiple
non-destructible aggregate locals, broader nested lifetime combinations,
virtual dispatch, general inheritance, bit-fields, nested record construction,
and same-named record layouts remain explicit errors.
Nested scalar locals, references to scalar locals, shadowing,
broader address-taking, pointer locals, pointer arithmetic outside the supported
indexed native object-pointer slice, nonliteral null-pointer conversions, multiple
indirection, call results outside the supported initializer, return-call and direct Boolean
condition slices,
indirect calls, loops,
external specifications other than the [standard-library
contracts](#c-standard-library), and broader C++ syntax also remain outside
this end-to-end subset.

## Validation and supported profile

Explicit refresh runs preprocessing with controlled arguments and environment,
records the selected toolchain, dependencies, source and artifact, and refuses
inputs that change during preparation. Ordinary loading does not invoke the
compiler. It checks the lock's internal identities and the available project
inputs against the recorded snapshot. Changed C sources, opened project-local
headers, configuration, or artifact bytes cannot reuse that lock. External
toolchain and header changes require a new explicit refresh to produce a proof
about that new environment. A supplied digest alone does not authenticate who
prepared a native-platform artifact.

Compiler-backed C imports accept two explicit targets. The config target must
match the sidecar's target, from its `target` directive or `click.project.json`;
without either the sidecar selects the default `x86_64-linux-userspace`, so a
kernel-target config needs one of them. Prepared imports retain their target through verification and expansion.

| Target | Fixed compiler profile |
| --- | --- |
| `x86_64-linux-kernel` | GCC, `-x c`, `-std=gnu11`, `-m64`, `-funsigned-char`, `-nostdinc`. |
| `x86_64-linux-userspace` | GCC, `-x c`, `-std=c11`, `-m64`, `-fsigned-char`, `-nostdinc`, `-pthread`, `-D_POSIX_C_SOURCE=200809L`. |

The user-space profile checks C11, POSIX and pthread feature macros as well as
the LP64, eight-bit-byte, signed-char ABI: the probe requires that `__CHAR_UNSIGNED__` is not defined. It does not define `__KERNEL__`.
Configuration cannot override its fixed standard or profile macros. Target and
invocation identities distinguish locks even when the emitted C is identical.
Selecting this profile grants no pthread contract or concurrency semantics.

Both profiles disable ambient system include search with `-nostdinc`, so the
compiler never reads the host's C library headers. Supply the program's own
header roots with ordered `-iquote`, `-I`, or `-isystem` arguments; those
roots and opened headers participate in the preparation inventory and lock
identity. A standard library interface is not such a root, per the
[interface boundary](#interface-boundary): `#include <string.h>` finds
[Click's system headers](#clicks-system-headers), which the import adds after
every configured directory. Lock preparation may succeed while Click's C
parser still refuses an unsupported declaration in an included header.

### Click's system headers

During `click import lock`, Click writes its system headers for the selected
target to a private temporary directory and passes it as the last `-isystem`
directory, after the configuration's arguments. That is the place GCC and
Clang give the C library's headers, so their usual search order applies:

1. `#include "file.h"` searches the including file's directory, then the
   `-iquote` directories.
2. Both forms then search the `-I` directories, then the configured
   `-isystem` directories, in order.
3. Last come Click's headers.

The modeled headers have the same text, and the same meaning, as in direct
mode: `<stdint.h>`, `<inttypes.h>`, `<stdbool.h>`, and `<limits.h>` on both
targets, and `<stddef.h>`, `<string.h>`, and `<stdlib.h>` on the user-space
target. See the [C system headers](../language/c.md#system-headers) table.
`<pthread.h>` and `<stdatomic.h>` belong to the modeled-pthread runtime,
which refuses compiler-imported sources, so an import refuses them by name.

A header Click does not model is refused. On the user-space target, each
other header of C11 and POSIX.1-2017, such as `<stdio.h>`, `<ctype.h>`, or
`<sys/types.h>`, exists and stops preparation with an `#error` naming it, so
`__has_include(<stdio.h>)` is true, as it is with a C library, and a program
cannot silently take a branch its real build would not take. A header that is
in neither set, such as `<openssl/ssl.h>`, is missing; the compiler's
`No such file or directory` error is followed by a note listing the headers
Click supplies for the target. The kernel target supplies only its four
freestanding headers, since a kernel build has no C library.

Click's headers declare functions; they carry no contracts. A call is
checked against Click's standard-library contract for the function's name,
whichever declaration the compiler selected, just as for a prototype the
program writes itself. A project header that GCC finds first is therefore
used as GCC would use it: a `limits.h` in a `-I` or `-isystem` directory
replaces Click's `<limits.h>`, and one that continues with
`#include_next <limits.h>` reaches Click's. A `-iquote` directory serves only
quoted includes. Such a project header is an ordinary locked project input,
and its macros and declarations are the program's; what Click trusts is
unchanged.

The artifact's line markers name Click's headers as `<string.h>`, not the
temporary directory, so a refresh reproduces the artifact byte for byte. The
lock records, beside the project dependencies, the name and SHA-256 of each
Click header the compiler opened, and a digest of the target's header set:
which names exist and whether each is modeled or refused, which decides what
an include or `__has_include` finds. Loading refuses a lock when either no
longer matches the running Click, so a change to Click's headers requires a
refresh.

Existing configurations that pin a C library's include directories with
`-isystem`, as `design/charon-trial/zlib/` does with GCC 14's and glibc's,
keep them: those directories precede Click's, so every header they supply is
read from them, a locked input like any other. Refreshing those configs
reproduces their committed artifacts byte for byte.

Configured forced includes and ordered `-D` and `-U` options select additional
preprocessing inputs. Other compiler options are rejected unless a named option
profile, described below, lists their exact spelling. Response files, plugins,
and execution hooks are always rejected. The compiler runs with a cleared environment;
only the configuration's supported variables are supplied. Use explicit
`SOURCE_DATE_EPOCH` when source depends on date/time macros.

Compiler invocation has output and time bounds, and failure or cancellation
stops its owned process group. Partial compiler output cannot become a
validated artifact. Dependencies come from the compiler's complete dependency
output, including configured system headers; source-map filenames are not a
substitute for that inventory.

The initial implementation snapshots the working directory, source directories,
and configured include roots before and after preprocessing. Keep them quiescent
during lock refresh. Root/configuration/output paths with symlink components are
rejected during preparation; dependencies resolving outside the declared roots
are also rejected. Output parent directories must already exist. A project is
limited to 512 MiB and 200,000 entries in its input-root inventory, 64 MiB per
artifact, 128 MiB of combined artifacts, and 1 MiB each for its configuration
and lock. Compiler
processes have a 30-second limit. Exceeding a limit is a diagnostic, never a
partial successful import.

Compiler imports initially reject incremental `--changed-since` requests and
do not use verification markers. Their proofs are checked through the same
engine used for ordinary verification, profiling, audit, and expansion.

### Option profile `linux-6.8-x86_64-kbuild`

A configuration may set `"option_profile"` to a named option profile. The
profile admits further options beside the preprocessing options above, and
only for its target. The lock records the profile name beside each source's
complete argument vector, and loading refuses a lock whose profile differs
from the configuration's.

The one profile, `linux-6.8-x86_64-kbuild`, is the option set of the recorded
Linux v6.8.12 `x86_64_defconfig` Kbuild compilation of `lib/rbtree.c` with
GCC 13, for the `x86_64-linux-kernel` target. It exists for that in-repository
import. An option is accepted only where ignoring it cannot make Click accept
a program the compiler treats differently: the option affects only
preprocessing, whose result is the locked artifact, or only diagnostics, or
only code generation, or it makes the compiler's semantics stricter than
Click's or no weaker. The list is closed and keyed to exact spellings. A
different value, an unlisted sibling, or an unknown option is refused with its
source and argument position, for example
``source `lib/rbtree.c`: unsupported compiler argument 50 `-O3`; ...``. Some
options are accepted only beside others that make them safe; without them the
option is refused with the missing one named.

Besides `-E` and the source operand, which the importer supplies itself, the
recorded vector has 102 options: 15 base preprocessing options, 4 that the
target fixes, and 83 others with 79 distinct spellings. All 79 are accepted:
`-mno-sse` and `-mno-sse2` only beside `-mno-80387`, and `-O2` only beside
`-fno-strict-aliasing`, `-fno-strict-overflow`, and
`-fno-delete-null-pointer-checks`, with the optimizer promises below refused
in the imported source.

| Recorded option | Verdict | Reason |
| --- | --- | --- |
| `-I<dir>` (7) | Base | Include search; the files read are in the lock. |
| `-include <file>` (3) | Base | Forced include; the files read are in the lock. |
| `-D<macro>` (5) | Base | Macro definition; its effect is in the artifact. |
| `-nostdinc` | Fixed | The target's own argument. |
| `-std=gnu11` | Fixed | The target's own argument; Click's kernel C is GNU C11. |
| `-funsigned-char` | Fixed | The kernel target's own argument; its plain `char` is unsigned. |
| `-m64` | Fixed | The target's own argument; Click's ABI is LP64. |
| `-fmacro-prefix-map=./=` | Accepted | Rewrites the paths `__FILE__` expands to, in the artifact; Click refuses `__builtin_FILE`. |
| `-Wall` | Accepted | Diagnostics only. |
| `-Werror` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Werror=date-time` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Werror=designated-init` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Werror=implicit-function-declaration` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Werror=implicit-int` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Werror=incompatible-pointer-types` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Werror=return-type` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Werror=strict-prototypes` | Accepted | Diagnostics only; it can only make the compiler refuse. |
| `-Wcast-function-type` | Accepted | Diagnostics only. |
| `-Wenum-conversion` | Accepted | Diagnostics only. |
| `-Wframe-larger-than=2048` | Accepted | Diagnostics only. |
| `-Wimplicit-fallthrough=5` | Accepted | Diagnostics only. |
| `-Wmissing-declarations` | Accepted | Diagnostics only. |
| `-Wmissing-prototypes` | Accepted | Diagnostics only. |
| `-Wundef` | Accepted | Diagnostics only. |
| `-Wvla` | Accepted | Diagnostics only. |
| `-Wno-address-of-packed-member` | Accepted | Diagnostics only. |
| `-Wno-alloc-size-larger-than` | Accepted | Diagnostics only. |
| `-Wno-array-bounds` | Accepted | Diagnostics only. |
| `-Wno-dangling-pointer` | Accepted | Diagnostics only. |
| `-Wno-format-overflow` | Accepted | Diagnostics only. |
| `-Wno-format-security` | Accepted | Diagnostics only. |
| `-Wno-format-truncation` | Accepted | Diagnostics only. |
| `-Wno-frame-address` | Accepted | Diagnostics only. |
| `-Wno-main` | Accepted | Diagnostics only. |
| `-Wno-maybe-uninitialized` | Accepted | Diagnostics only. |
| `-Wno-missing-field-initializers` | Accepted | Diagnostics only. |
| `-Wno-override-init` | Accepted | Diagnostics only. |
| `-Wno-packed-not-aligned` | Accepted | Diagnostics only. |
| `-Wno-pointer-sign` | Accepted | Diagnostics only. |
| `-Wno-restrict` | Accepted | Diagnostics only. |
| `-Wno-shift-negative-value` | Accepted | Diagnostics only. |
| `-Wno-sign-compare` (twice) | Accepted | Diagnostics only. |
| `-Wno-stringop-overflow` | Accepted | Diagnostics only. |
| `-Wno-stringop-truncation` | Accepted | Diagnostics only. |
| `-Wno-trigraphs` | Accepted | Diagnostics only; GNU C11 does not replace trigraphs. |
| `-Wno-type-limits` | Accepted | Diagnostics only. |
| `-Wno-unused-but-set-variable` (twice) | Accepted | Diagnostics only. |
| `-Wno-unused-const-variable` (twice) | Accepted | Diagnostics only. |
| `-fno-common` | Accepted | GCC 13's default; a tentative definition is one zero-initialized definition, as Click models it. |
| `-fno-delete-null-pointer-checks` | Accepted | Stops GCC assuming that a dereferenced pointer is not null; Click refuses any access through a possibly null pointer. |
| `-fno-strict-aliasing` | Accepted | Removes GCC's type-based alias assumptions; Click never assumes them, and refuses accesses that do not fit the cell. |
| `-fno-strict-overflow` | Accepted | Makes signed and pointer overflow wrap; Click treats both as undefined, which is stricter. |
| `-fshort-wchar` | Accepted | Changes `wchar_t` and the wide-literal element type; the predefines are in the artifact and Click has no wide literals. |
| `-fstrict-flex-arrays=3` | Accepted | Only `[]` is a flexible member; Click has no flexible or zero-length members and bounds every struct array by its declared length. |
| `-ftrivial-auto-var-init=zero` | Accepted | Zeroes uninitialized automatic storage; Click refuses any read of uninitialized storage. |
| `-fno-allow-store-data-races` | Accepted | GCC 13's default; forbids invented stores, so it only removes transformations. |
| `-falign-functions=16` | Accepted | Code layout only. |
| `-falign-jumps=1` | Accepted | Code layout only. |
| `-falign-loops=1` | Accepted | Code layout only. |
| `-fcf-protection=branch` | Accepted | Adds `endbr64` landing pads; its `__CET__` predefine acts only through preprocessing. |
| `-fconserve-stack` | Accepted | Inlining and frame-size heuristics only. |
| `-fno-PIE` | Accepted | Position-dependent code; dropping `__pie__` and `__PIE__` acts only through preprocessing. |
| `-fno-asynchronous-unwind-tables` | Accepted | Omits unwind tables only. |
| `-fno-jump-tables` (twice) | Accepted | Switch lowering only. |
| `-fno-stack-check` | Accepted | Stack probing only. |
| `-fno-stack-clash-protection` | Accepted | Stack probing only. |
| `-fomit-frame-pointer` | Accepted | Frame layout only; Click refuses `__builtin_frame_address`. |
| `-fpatchable-function-entry=16,16` | Accepted | Padding before function entry only. |
| `-fstack-protector-strong` | Accepted | Adds stack canaries; Click refuses the overflows they detect. |
| `-mcmodel=kernel` | Accepted | Code and data addresses in the top 2 GiB; Click assumes nothing about address values beyond null. |
| `-mfunction-return=thunk-extern` | Accepted | Return thunks only. |
| `-mindirect-branch-cs-prefix` | Accepted | Instruction encoding only. |
| `-mindirect-branch-register` | Accepted | Indirect-branch code generation only. |
| `-mindirect-branch=thunk-extern` | Accepted | Indirect-branch thunks only. |
| `-mno-3dnow` | Accepted | Restricts instruction selection; no floating-point evaluation change. |
| `-mno-80387` | Accepted | Floating point uses no x87; it fails to compile or calls libgcc's IEEE routines, without excess precision. |
| `-mno-avx` | Accepted | Restricts instruction selection; no floating-point evaluation change. |
| `-mno-fp-ret-in-387` | Accepted | Return convention for x87 values, which Click has no operations on. |
| `-mno-mmx` | Accepted | Restricts instruction selection; no floating-point evaluation change. |
| `-mno-red-zone` | Accepted | Stack layout only. |
| `-mno-sse` | Accepted with `-mno-80387` | Alone it moves floating point to the x87 with excess precision (`__FLT_EVAL_METHOD__` 2), which Click does not model. |
| `-mno-sse2` | Accepted with `-mno-80387` | Alone it moves `double` to the x87 with excess precision (`__FLT_EVAL_METHOD__` -1), which Click does not model. |
| `-mpreferred-stack-boundary=3` | Accepted | Stack alignment only; GCC realigns frames that need more. |
| `-mskip-rax-setup` | Accepted | Variadic-call register setup only. |
| `-mtune=generic` | Accepted | Instruction scheduling only. |
| `-O2` | Accepted with `-fno-strict-aliasing`, `-fno-strict-overflow`, `-fno-delete-null-pointer-checks` | Optimization preserves the meaning of a program without undefined behavior, which is what Click proves; GCC's remaining unchecked assumptions are refused in the source (see "Optimizer promises"), and `__builtin_constant_p` is an unknown 0 or 1. |

### Optimizer promises

Under an option profile that accepts optimization, the frontend refuses, with
the attribute's location and the reason, every attribute and qualifier that
GCC's optimizer trusts as a promise from the programmer, because Click does not
check those promises. Without such a profile, GCC 13 does not act on them and
they are accepted and ignored as before.

| Construct | Under `linux-6.8-x86_64-kbuild` | Reason |
| --- | --- | --- |
| `nonnull` | Refused | GCC deletes the parameter's null checks, even with `-fno-delete-null-pointer-checks`. |
| `const` | Refused | GCC merges calls and assumes the function touches no memory. |
| `leaf` | Refused | GCC assumes the call leaves the unit's unescaped static data unchanged. |
| `access` | Refused | A promise about how the pointed-to object is accessed; not observed exploited by GCC 13, but unchecked. |
| `noreturn` | Refused, except on `compiletime_assert`'s block-scope `error` declaration | GCC emits nothing after the call. Every call to an `error` declaration lowers to a check that fails on any path reaching it, so Click proves it unreachable. |
| `returns_twice` | Refused | A second return needs a control-flow model Click does not have. |
| `restrict` | Refused | GCC assumes restrict pointers do not alias. |
| `pure`, `returns_nonnull`, `malloc`, `alloc_size`, `alloc_align`, `assume_aligned` | Refused in every mode | Unchecked promises the frontend never accepted. |
| `__builtin_unreachable`, `__builtin_assume`, `assume` statement attribute | Refused in every mode | Unchecked promises the frontend never accepted. |
| `cold`, `hot`, `noinline`, `warn_unused_result`, `nonstring` | Refused in every mode | Harmless to the optimizer's semantics (layout, inlining, and diagnostics only), but not supported by the frontend. |
| `always_inline`, `gnu_inline`, `nothrow`, `weak`, `deprecated`, `unused`, `no_instrument_function` | Accepted | Inlining choice, linkage, or diagnostics; C has no exceptions for `nothrow` to promise about. |
| `__builtin_expect` | Accepted | A branch-probability hint; its value is its first operand. |

The list comes from GCC 13's attribute documentation and from these
measurements with the recorded `x86_64-linux-gnu-gcc-13`. Each lying
declaration is in a separate object file, so GCC cannot see the body, and each
program prints the same values at `-O0` and differs at `-O2` with the three
safety options:

- `nonnull(1)` on a definition with `if (!p) return -1;`: `-O0` returns -1
  for a null argument, `-O2` dereferences it and crashes.
- `const`, and `pure` on a function that increments a counter: two calls
  differ by 1 at `-O0`, and by 0 at `-O2`.
- `leaf` on a function that calls back into the unit and changes a static
  variable: `-O0` sees the change, `-O2` does not.
- `noreturn` on a function that returns: `-O0` continues after the call,
  `-O2` runs off the end of the caller and crashes.
- `restrict` parameters passed the same address: `-O0` reads the second
  store, `-O2` the first.
- `malloc` on a function returning an existing object's address: `-O2`
  misses the store through the result.
- `assume_aligned(16)` on a misaligned pointer: `-O2` folds the low bits to 0.
- `__builtin_unreachable` and `assume` statement attributes: `-O2` folds
  the condition they assert.
- `returns_nonnull` returning null: the check is deleted at `-O2` without
  `-fno-delete-null-pointer-checks` and kept with it.
- `access(read_only, 1)` on a function that writes, and `__builtin_expect`:
  no difference.

GCC does not assume that loops terminate when compiling C (`-ffinite-loops`
is off), and `-O2` otherwise exploits only undefined behavior, such as
signed overflow, null or out-of-bounds access, and reads of uninitialized
storage, which Click refuses to prove. The three safety options turn off the
remaining assumptions Click does not make: type-based aliasing, overflow, and
null-check deletion.

## C++ standard library

A function declared in a system header (one reached through `-isystem`, a
system include path, or `#pragma clang system_header`) is an axiom. The
exporter records its kind, receiver, parameters and return type, keyed by its
qualified name and canonical signature, and never exports its body. Click
prepares it as an opaque function, and each call is checked against a
contract:

- Click supplies contracts for the standard functions in its catalog, keyed on
  the standard name and signature, so a proof does not depend on whether
  libstdc++ or libc++ was parsed. The sidecar is parsed with them appended; the
  catalog itself is never written into a sidecar by expansion.
- A call to a standard function with no catalog contract is refused, naming
  the function. A sidecar may state its own `extern` contract instead, which is
  an assumption like any other external contract.
- A standard function must be `noexcept`; throwing contracts are not modeled.
  One returning a record by value constructs it in the caller's destination.

Contracts state a standard type's state through model accessors, never
through a library's private fields. `std_span_data(s)` and `std_span_size(s)`
name the data pointer and size of a `std::span`, the view of
`[data, data + size)`, and `std_array_data(a)` names the elements a
`std::array` holds. The parser rewrites an accessor into the one field path
of the library that was parsed (libstdc++'s `_M_ptr`,
`_M_extent._M_extent_value` and `_M_elems`, or libc++'s `__data_`, `__size_`
and `__elems_`), and checks it like a written field access; an argument of
another type is refused there. A layout that matches neither library, or
matches both, binds no accessor, so an accessor is never misbound. A libc++
program verifies with the same proofs as a libstdc++ one
(`tests/libcxx_span.rs`, against the pinned closure in
`tests/fixtures/libcxx-span`). An accessor works wherever a field
does, as in `owns std_span_data(s);`. Diagnostics and expanded proofs print the
accessor for its field path, so an expanded proof names no private field
either.

A refused catalog precondition reached after execution also names reads by
these accessors. Historical reads keep their snapshot qualification, for
example `at(<state A>, std_span_size(s))`, rather than a carrier-cell index.

The `std::span<T>` entries are generic over the element type `T`, which may
be `int`, `unsigned int`, `unsigned char` or `std::byte`, each possibly
`const`; a `std::span<const T>` holds a `const T*`, and its element accessors
return `const` references. They cover a
dynamic-extent span's `size`, `size_bytes`, `data`, `front`, `back`,
`operator[]`, `first`, `last` and `subspan(offset, count)`:

A dynamic-extent `subspan` retains the catalog's implication-shaped count
precondition. Before recovering its returned view, implicit `auto` proves
any pending call requirement at the caller's pre-state, including a count
implication with a false antecedent. Expansion retains that proof as an
explicit step requirement; recovery still refuses unproved requirements.

| Member | Requires | Ensures |
| --- | --- | --- |
| `size()` | | `result == std_span_size(s)` |
| `size_bytes()` | | `result == std_span_size(s) * sizeof(T)` |
| `data()` | | `result == std_span_data(s)` |
| `front()`, `back()` | `1 <= size` | the first or last element's address |
| `operator[]`, index `i` | `i < size` | `&result == std_span_data(s) + i` |
| `first(n)` | `n <= size` | data unchanged, size `n` |
| `last(n)` | `n <= size` | data `+ (size - n)`, size `n` |
| `subspan(o, n)` | `o <= size`; `n != std::dynamic_extent implies n <= size - o` | data `+ o`; size `n`, or `size - o` for `std::dynamic_extent` |

An element type outside that list matches no entry, so its calls are refused
by name. Element accessors (`front`, `back`, `operator[]`) return native
element references, which a caller may bind, read or write directly.
A defaulted argument is imported as the constant Clang evaluates for it, so
`subspan(1)` passes `std::dynamic_extent` as its count and verifies as the
subview to the end.

A static-extent `std::span<T, N>` keeps its extent in its type. libstdc++'s
extent member is `[[no_unique_address]]` and empty, so the importer leaves it
out and the record holds only the data pointer; any such stateless member of
an empty, trivially copyable class is left out the same way. Its entries
state the size as the literal `N`: `size()` is `N`, `size_bytes()` is
`N * sizeof(T)`, and `front`, `back` and `operator[]` require an index below
`N`. `first`, `last` and `subspan` take a runtime count and return
dynamic-extent spans.

`std::array<T, N>` holds its elements in an inline array field, which the
record profile admits for native element types. Its `size()` is `N`; `data()`
is `&std_array_data(a)[0]`; and `front`, `back` and `operator[]`, in their
const and mutable overloads, require an index below `N` and return
`&std_array_data(a)[i]`. A read needs a resource for the array and a write
needs to own it. A resource clause naming one element through a reference
parameter is refused by a defect
(`bugs/a-reference-records-array-element-resource-does-not-lower.md`); naming
the whole array works.

The catalog also covers dynamic-extent
`std::as_writable_bytes(std::span<int>)`. It returns a byte view of the
same storage: its data is `(uint8*)std_span_data(input)` and its native uint64
length is `std_span_size(input) * 4u64`. It copies no backing bytes, requires no
backing ownership, and establishes no backing initialization or write permission.
The integer-to-byte pointer cast preserves allocation identity and lifetime.
Both const-reference and by-value callers have ordinary, expanded and retained
proof coverage for the pointer and length relations. The by-value proof preserves
the result pointer relation when private parameter storage is retired.
Element accessors require an index inside the view,
as the standard does, and form an address without reading it. Bitcoin Core's
unchanged `SpanPopBack` verifies against these contracts
(`tests/bitcoin_core_money_range.rs`). Proofs assume a C++ standard library
that implements Click's contracts.

## Dependency-closure projection

A source entry may set `"projection": "dependency-closure"`. Click then
imports only part of the locked artifact: every function definition written
in the translation unit's own source file (the file the first line marker
names), and, transitively, every file-scope declaration that defines a name a
kept declaration mentions. That includes types, struct, union, and enum tags,
enumeration constants, typedefs, objects, prototypes, and inline helpers.
Everything kept is parsed, lowered, and checked as usual, so an unsupported
construct inside the closure is still rejected with its original location.
Declarations outside the closure are not parsed, and nothing is claimed about
them.

Two rules keep the omission checked rather than permissive:

- An exact `extern typeof(f) f;` redeclaration is never needed to type a use
  of `f`, because it repeats `f`'s own type with nothing added. The Linux
  `EXPORT_SYMBOL` macro emits one per exported function, beside its export
  storage and `.export_symbol` assembly, which nothing names. Export storage
  and export assembly are therefore outside the claim.
- If an omitted declaration carries the `constructor` or `destructor`
  attribute, the projection is refused, because such a function runs
  without being named.

Every other declaration that defines a needed name is kept, including
redeclarations that add attributes such as `weak`. Omitted declarations are
blanked in place, so line numbers and original-source locations are
unchanged. The option is part of the import configuration and therefore of
the lock's identity.

This is a bounded arrangement for importing one kernel translation unit
whose headers declare far more than its functions use. It is not a general
statement that omitted header declarations are harmless, and it does not
validate them.

## Locations and trust boundary

Structured compiler line markers preserve original filenames and line numbers
through parsing and lowering. Physical artifact positions remain available for
debugging. Textual markers do not provide full macro-expansion backtraces or
exact original columns inside expanded macros; diagnostics do not claim that
precision. A system-header marker does not suppress errors or omit code.

The compiler preprocessor is a trusted dependency for source selection.
Reproducing its invocation is not a formal proof that its preprocessing is
correct. It supplies neither executable C semantics nor proof authority to
Click: those remain in Click's frontend and independent kernel checker.

The captured Linux 6.8.12 rbtree translation unit is locked in
`integrations/linux-rbtree/`. Its configuration selects the
`linux-6.8-x86_64-kbuild` option profile and the dependency-closure
projection. Its full header graph includes unsupported C forms, effectful
assembly, and storage-producing exports, which the projection leaves out. The
lock and artifact load offline once the checked input closure is extracted;
no proof runs against the imported bodies yet.

## Options and exit status

`--help` and `-h` show usage. `--` ends option parsing before a positional path.
A successful lock operation exits 0. Invalid configuration, missing inputs,
compiler failure, an exceeded bound, or an output-write failure exits nonzero
with a diagnostic. Ordinary verification never rewrites a lock or artifact.


C++ imports may explicitly assume a narrow external library assertion contract
with the optional `library_assertions` config field. For example (replace the
hash with the SHA-256 of the actual header bytes):

```json
"library_assertions": [{
  "kind": "checked_boolean_statement",
  "function": "library::check",
  "header": "gate.h",
  "sha256": "<64 lowercase hexadecimal digits>"
}]
```

The header must be in the explicit `dependencies` inventory and the locked
preprocessor closure. Entries have unique, sorted qualified function names;
the inventory is limited to 64. Header hashes are checked during refresh and
offline loading. The resolved callee declaration, and its definition when
present, must belong to that header. Definitions in the selected logical
source still require ordinary verified contracts, including recursive calls.
Config, artifact, compiler command, and input closure are part of the import identity. A changed pin requires an
explicit config edit and lock refresh.

This is an **assumed library contract**, not verification of its implementation.
It states that, when its Boolean argument is true, the call returns normally with defined behavior
without changing caller-visible memory. Each admitted call evaluates that
argument and generates an obligation to prove it true. It neither adds an
unproved condition to the proof context nor admits the library's false-input,
abort, or exception behavior. The diagnostic names the contract and header
hash; normal cleanup still runs. A function merely named `Assume` retains
ordinary call semantics without a matching explicit contract.

The `checked_boolean_statement` kind accepts a direct standalone discarded-result
call to a free, non-template, non-variadic function with one Boolean value
parameter and a void or Boolean value return type. Its argument may compare
supported scalar values and nonvolatile data fields, and combine those conditions
with `&&`. Field reads are evaluated with ordinary memory authority and
initialized-value obligations; the library contract does not grant access to
them. Mutation, calls, general pointer dereferences, and partial arithmetic are
refused. This kind does not admit metadata, references, or templates.

The separate `checked_boolean_statement_with_consteval_metadata` kind adds
resolved templates using the existing Boolean/scalar template-argument profile,
a Boolean rvalue-reference parameter, and a discarded Boolean rvalue-reference
return. A reference condition must bind a Boolean prvalue, rather than a caller
lvalue or cast-to-reference expression. The same checked-condition proof obligation
applies, including memory authority for evaluated field reads. The assumed library behavior must hold for every admitted specialization
and metadata value; metadata contents are not proved or used to establish the
condition.

Up to eight further arguments may be direct, forced `consteval` call results of
the exact parameter type. Integer metadata binds by value or const reference.
Record metadata binds only by const reference and must have a trivial destructor.
No runtime conversion, record value parameter, nontrivial temporary cleanup, or
use of the library return is admitted. A `constexpr` function being eligible for
constant evaluation is insufficient: its runtime execution may have effects.
Forced compile-time evaluation and harmless materialization are compiler
semantics under the locked profile, not an assumption that arbitrary metadata
functions are pure at runtime.

The artifact retains the resolved specialization and each metadata factory's
qualified name and canonical declaration file. Offline validation checks the
contract kind, bounded metadata inventory, and declaration-file membership in
the locked preprocessor closure. Artifact schema 45 requires an explicit refresh
of earlier locks.

The separate `checked_boolean_statement_with_literal_metadata` kind adds a
single, independently pinned `literal_constructor` contract, for example:

```json
{
  "kind": "checked_boolean_statement_with_literal_metadata",
  "function": "library::check",
  "header": "gate.h",
  "sha256": "<SHA-256 of gate.h>",
  "literal_constructor": {
    "function": "library::Text::Text",
    "header": "text.h",
    "sha256": "<SHA-256 of text.h>"
  }
}
```

Both headers must be explicit dependencies and belong to the locked preprocessor
closure. The constructor contract separately assumes that construction from an
admitted literal returns normally with defined behavior and no caller-visible
memory effects. Its implementation is not verified. The qualified constructor
family names the class and constructor, without template arguments; the assumption
covers every admitted specialization, whose resolved record type remains in the
artifact. Selected-source constructor definitions cannot use this boundary.

Each runtime metadata construction must initialize the exact record parameter
type from one direct narrow string literal, via a single `const char*` parameter.
The literal is limited to 4,096 ASCII bytes without embedded NULs; its compiler
provided terminating NUL and static lifetime remain available during the call.
Runtime pointers, conversions, default arguments, additional constructor
arguments, and argument effects are rejected. A record binds by value or const
reference, requires trivial destruction, and by-value parameters additionally
require a trivial copy constructor. C++20 direct initialization from a prvalue
constructs the parameter without executing a user-defined copy or move. The
exporter checks the actual constructor and harmless materialization; it does not
treat a runtime `constexpr` constructor as a forced compile-time operation.

The artifact distinguishes `consteval` and `literal` metadata and retains the
literal bytes, resolved record type, binding, constructor pin, and canonical
declaration file. Offline validation binds that file to the exact pinned
constructor dependency as well as the preprocessor closure. Proof diagnostics
expose both the assertion and constructor assumptions. Metadata supplies no
proof facts; all calls still require the same proven Boolean condition.

Bitcoin's unchanged annotation has separate missing-contract and consteval-only
refusal regressions, plus a new opt-in contract that pins the standard-library
string-view constructor. This imports and lowers the complete unchanged
`FeeFrac::Div`; missing condition, wide arithmetic guards, and narrow correction
bounds still fail verification. Its general division/rounding theorem remains
open.


C++ statement attributes `[[likely]]` and `[[unlikely]]` affect optimization
weights only and preserve the checked branch or statement behavior. The exporter
unwraps those attributes before lowering the original statement or branch body;
other statement attributes, including `[[clang::musttail]]`, are rejected.
The unevaluated `__builtin_assume` continues to require a total scalar condition
without memory reads. Evaluated, explicitly pinned library assertions use the
separate field-reading boundary described above.
