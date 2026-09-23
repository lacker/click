# `click import`

Compiler imports let a sidecar verify the C selected by a configured compiler
preprocessor. Click still parses and lowers the resulting C and independently
checks its proofs. This mode is explicit and separate from the existing bounded
source-bundle preprocessor. The same command also refreshes the preliminary
typed C++ artifact described below.

```text
usage: click import lock <sidecar.click>
```

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
configured compiler. The artifact and version-2 lock can move to another host
with the same config bytes, C source, and project-local included headers. Loading
checks their hashes, the artifact bytes and size, the target, the recorded
toolchain/invocation identity, and the source projection identity. System
headers used during preparation are identified in the lock but need not be
installed on the verification host. A version-1 C lock must be refreshed.

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
selected free function and the uniquely named free-function definitions
reachable from its supported direct call statements. In the baseline profile,
exceptions are disabled and every selected or reachable function must declare
`noexcept`. A second, deliberately smaller profile may retain the compilation
command's enabled exception mode: free functions may omit `noexcept`, but the
entire closed reachable graph must remain object-free and contain only Click's
already checked normal-returning operations.
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
artifact. These booleans may also be true for an object-free, normal-only
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
reachable `throw`, `try`/`catch`, unresolved calls, and every record/object use
are rejected locally. Because the artifact contains the complete supported
direct-call closure and has no throwing operation, ordinary verification may
check its normal behavior without inventing an exceptional proof outcome.
An RTTI-enabled profile is similarly allowed only for the currently supported
object-free graph; this does not add `typeid` or `dynamic_cast` semantics.

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
One narrow unwinding case is also supported: a `try` block may construct one
destructible automatic guard first, then call a potentially throwing helper.
Its public, non-virtual constructor and destructor must be explicitly
`noexcept`; the destructor runs on both normal and exceptional exits before
the handler observes state. The constructor's Click contract must establish
any object invariant required by the destructor that is not already available
from the checked execution state. The `cpp_one_guard_unwind` mdtest verifies
both outcomes.
The importer still rejects nested handlers, catch-all or non-`int` handlers,
other local declarations inside either block, multiple or late guards, returns
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

The first proof-facing interface uses existing Surface Click pointer syntax
for the reference's one-cell mutable view:

<!-- verified-example: examples/basic-cpp/increment.click -->
```click
verifying "increment.cpp";

int32 increment(int32* value) {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures value[0] == old(value[0]) + 1;
    ensures result == value[0];
} by {
    execute();
    simp();
}
```

This spelling does not translate the C++ body to C. The sidecar signature is
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
currently by-value `bool`, `int&`, `const int&`, mutable `int*`, one `const`
signed-64 reference, and a mutable reference to the one supported simple record
type. Selected functions return `int` or `bool`.

The `int64-predicate` fixture is the first narrow bridge toward Bitcoin Core's
`MoneyRange`: Clang retains the declaration identity and source span for a
direct `typedef long CAmount`, lowers `const CAmount&` as a const `int64*`,
retains the implicit `int`-to-signed-64 conversion of zero, and returns the
Boolean result of signed `>=`. Its exact all-input contract states the result
with a conditional expression and verifies offline:

<!-- verified-example: tests/fixtures/cpp-verification/int64-predicate/money_nonnegative.click -->
```click
verifying "money_nonnegative.cpp";

bool money_nonnegative(const int64* nValue) {
    owns nValue[0..1];
    ensures result == (if old(nValue[0]) >= 0i64 { 1 } else { 0 });
} by {
    if nValue[0] >= 0i64 {
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
unsigned 64-bit aliases, other relational operators, `||`, overloaded logical
operators, and non-Boolean `&&` operands remain outside the boundary.

The `direct-call` fixture selects a caller and captures the transitive closure
of definitions reached by discarded-result direct call statements. Each call
node records the declaration identity resolved by Clang, reference arguments
retain their parameter identity, and all captured functions lower into the
ordinary modular call environment. Each definition has its own sidecar
contract and proof. The artifact rejects recursion, ambiguous reachable names,
and missing definitions. Reachable functions that omit `noexcept` are accepted
only in an exception-enabled, object-free profile; the baseline profile
continues to reject them. Omitting `noexcept` does not itself declare a Click
exception.

The `scalar-local` fixture adds mutable automatic `int` locals declared directly
in the function body. Each local requires an initializer, which may be an
already-supported integer expression or a supported direct call. Local
declaration identity comes from Clang; direct-call initialization lowers to the
kernel's ordinary `Declare` and `CallAssign` statements, while later reads and
assignments use the existing scalar rules. This makes call results usable
without treating a compiler-resolved C++ expression as C source text.

The `pointer` fixture distinguishes a mutable `int*` parameter from an `int&`
in the Clang artifact. A caller may take the address of its mutable reference
parameter and pass that pointer to a direct call. Pointer lvalue-to-rvalue
conversion, `*pointer` reads, and `*pointer = value` writes lower to the
kernel's existing address, typed-load, and typed-store operations, so the
sidecar must provide ordinary memory authority. Removing that authority or
claiming the wrong pointer-mediated memory effect fails verification.

The `struct-member` fixture accepts one named, public, non-inheriting aggregate
`struct` whose fields are mutable `int` or mutable `int*`. Clang supplies the
record and field declaration identities plus the exact LP64 size, alignment,
field offsets, and field widths. A function may receive an existing object by
mutable reference and read or write those fields with `object.field`; a pointer
loaded from a field may use the already-supported checked dereference rules.
The proof interface spells that reference as `struct Name*` and uses ordinary
field resources such as `owns state->saved`. Click does not reconstruct the
layout from C++ source or create a synthetic C body.

The `local-aggregate` fixture declares one automatic object of that same record
kind directly in a function body. It must use direct braces with exactly one
initializer for every field in declaration order. The artifact binds those
expressions to Clang field identities, and direct lowering allocates the exact
Clang layout as kernel stack memory before applying typed field stores. Later
`object.field` reads use the same checked offsets as an existing object passed
by reference; trivial scope exit needs no destructor action.

The `constructor-local` fixture permits that one automatic object to use one
public, explicit, non-default `noexcept` constructor. Its member-initializer
list must initialize every field in declaration order; the constructor body
and its implicit call at the declaration are both lowered and verified through
the ordinary modular call rules.

The `terminal-destructor` fixture adds one public, non-virtual, non-deleted,
explicitly `noexcept` destructor with a nonempty supported body. The artifact
records its declaration identity on the record and records its implicit call
as cleanup on the function's single final return. Direct lowering first
captures the return expression in an internal scalar local, then calls the
checked destructor, then returns the captured value. The fixture proves that
the destructor restores caller memory while the result retains the value seen
before cleanup; missing and false destructor contracts are rejected.

The `early-return-destructor` fixture permits structured `if` statements after
one destructible object has been constructed directly in the function body.
Every return edge captures its result and then invokes that same checked
destructor. It verifies the original two-path `Restore` example: the early path
returns 7, the final path returns 9, and both restore the referenced integer to
its entry value. A return before construction is rejected rather than assigned
a cleanup for an object that is not alive.
The `examples/basic-cpp/` project also selects a modular caller starting with
41: either captured result is retained while the referenced cell is 41 after
the call.

The `reverse-destructor-order` fixture permits exactly two such top-level
objects when both use the supported constructor and destructor. Both objects
must be constructed before any return. Each return records the second object's
destructor before the first object's destructor, and lowering checks those
calls in that order. The fixture makes the ordering observable: the second
guard restores 7 before the first guard restores the caller's entry value.

The `nested-scope-destructor` fixture alternatively permits one explicit block
directly in a free-function body, with exactly one directly constructed
destructible object and no other block local. A return from the block captures
its value before running the destructor, while normal fallthrough runs the
same checked cleanup before the next outer statement. The artifact retains
that lexical boundary as a `scope` statement; the outer return consequently
has no cleanup for the already-destroyed object.

The `sibling-scope-destructors` fixture composes up to two such blocks when
their object lifetimes do not overlap. Each sibling carries its own return and
fallthrough cleanup, and the next block begins only after the preceding
destructor. The fixture deliberately reuses the source name `guard`; distinct
Clang declaration identities and the kernel's sequential local-lifetime rule
keep the two objects separate.

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

Copies and moves, default or partial aggregate initialization, multiple or
more than two top-level destructible local objects, broader nested lifetimes,
ordinary methods, inheritance, private fields, bit-fields, nested records, and
multiple record types remain explicit errors.
Uninitialized or nested scalar locals, local references, shadowing,
address-taking other than a current mutable reference parameter for a supported
pointer call, pointer locals, pointer arithmetic, null pointers, multiple
indirection, call results outside a local initializer, indirect calls, loops,
external specifications, and broader C++ syntax also remain outside this
end-to-end subset.

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
match the sidecar's `target` directive; an omitted directive selects the kernel
target. Prepared imports retain their target through verification and expansion.

| Target | Fixed compiler profile |
| --- | --- |
| `x86_64-linux-kernel` | GCC, `-x c`, `-std=gnu11`, `-m64`, `-funsigned-char`, `-nostdinc`. |
| `x86_64-linux-userspace` | GCC, `-x c`, `-std=c11`, `-m64`, `-funsigned-char`, `-nostdinc`, `-pthread`, `-D_POSIX_C_SOURCE=200809L`. |

The user-space profile checks C11, POSIX and pthread feature macros as well as
the LP64, eight-bit-byte, unsigned-char ABI. It does not define `__KERNEL__`.
Configuration cannot override its fixed standard or profile macros. Target and
invocation identities distinguish locks even when the emitted C is identical.
Selecting this profile grants no pthread contract or concurrency semantics.

Both profiles require explicit include directories: `-nostdinc` disables
ambient system include search. Supply the selected toolchain and libc header
roots with ordered `-isystem` or `-I` arguments; those roots and opened headers
participate in the preparation inventory and lock identity. For the selected
Debian GCC 12 environment, these roots are `/usr/lib/gcc/x86_64-linux-gnu/12/include`,
`/usr/include/x86_64-linux-gnu`, and `/usr/include`. Other installations must
supply their actual selected roots. Lock preparation may succeed while Click's
C parser still refuses an unsupported declaration in a real system header.

Configured forced includes and ordered `-D` and `-U` options select additional
preprocessing inputs. Unsupported compiler options, response files, plugins,
and execution hooks are rejected. The compiler runs with a cleared environment;
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

The captured Linux 6.8.12 rbtree translation unit is not yet supported by this
first profile. Its full header graph includes unsupported C forms, effectful
assembly, storage-producing exports, and additional compiler options. The
kernel capture records those gaps; it is not a passing verification fixture.

## Options and exit status

`--help` and `-h` show usage. `--` ends option parsing before a positional path.
A successful lock operation exits 0. Invalid configuration, missing inputs,
compiler failure, an exceeded bound, or an output-write failure exits nonzero
with a diagnostic. Ordinary verification never rewrites a lock or artifact.
