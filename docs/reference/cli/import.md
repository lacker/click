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

Lock creation is source preparation, not proof verification. The C parser can
still reject an unsupported construct when a proof tool loads the prepared
translation unit. No C declarations, function bodies, storage, attributes, or
assembly are silently deleted to make an import pass.

## Preliminary C++ semantic artifact

The preliminary C++ frontend boundary accepts one header-free C++20 source with
one selected, explicitly `noexcept` free function and the uniquely named
`noexcept` free-function definitions reachable from its supported direct call
statements. The linear reference fixture is:

```cpp
int increment(int& value) noexcept {
    value = value + 1;
    return value;
}
```

Its import configuration explicitly sets `"language": "c++"`, the standard
to `c++20`, target to `x86_64-unknown-linux-gnu`, exceptions and RTTI to false,
and paths for the pinned exporter, working directory, `.cpp` source, logical
source, selected function, and semantic artifact. `click import lock` executes
the repository-owned Clang 19.1.7 LibTooling exporter and records the source,
exporter, profile, artifact, and configuration identities.

```json
{
  "schema": 1,
  "language": "c++",
  "standard": "c++20",
  "target": "x86_64-unknown-linux-gnu",
  "exceptions": false,
  "rtti": false,
  "exporter": "target/cpp-exporter/click-cpp-exporter",
  "working_directory": ".",
  "source": "increment.cpp",
  "logical_source": "increment.cpp",
  "function": "increment",
  "artifact": "increment.cpp.click-cpp.json"
}
```

Loading through the C++ library boundary subsequently validates the source,
lock, and typed artifact without locating or running Clang. This separation is
intentional: compiler execution belongs to explicit refresh. The library
lowers this exact artifact directly to the kernel execution vocabulary without
generating C text or invoking the C parser. An `int&` or `const int&` becomes an
address-valued parameter with its pointee qualification preserved. Reads become
typed loads, while only the mutable reference permits a typed store; signed
addition retains the kernel's existing overflow check. The lowered value
remains paired with the immutable semantic artifact so Clang declaration
identities and source spans are not discarded.

The first proof-facing interface uses existing Surface Click pointer syntax
for the reference's one-cell mutable view:

<!-- verified-example: tests/fixtures/cpp-verification/increment/increment.click -->
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
currently by-value `bool`, `int&`, `const int&`, mutable `int*`, and a mutable
reference to the one supported simple record type. Selected functions still
return `int`.

The `direct-call` fixture selects a caller and captures the transitive closure
of definitions reached by discarded-result direct call statements. Each call
node records the declaration identity resolved by Clang, reference arguments
retain their parameter identity, and all captured functions lower into the
ordinary modular call environment. Each definition has its own sidecar
contract and proof. The artifact rejects recursion, ambiguous reachable names,
missing definitions, and reachable functions that are not `noexcept`.

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
before cleanup; missing and false destructor contracts are rejected. Branches,
early returns, nested scopes, and more than one destructible automatic object
remain rejected until cleanup-edge ordering is represented generally.

Copies and moves, default or partial aggregate initialization, multiple or
nested local objects, ordinary methods, inheritance, private fields,
bit-fields, nested records, and multiple record types remain explicit errors.
Uninitialized or nested scalar locals, local references, shadowing,
address-taking other than a current mutable reference parameter for a supported
pointer call, pointer locals, pointer arithmetic, null pointers, multiple
indirection, call results outside a local initializer, indirect calls, loops,
external specifications, and broader C++ syntax also remain outside this
end-to-end subset.

## Validation and supported profile

Each load runs fresh preprocessing with controlled arguments and environment,
then compares the result and input identities with the existing lock. Changed
sources, used headers, toolchain inputs, configuration, or artifact bytes cannot
reuse an incompatible lock. Refreshing a lock is always a separate explicit
operation. A supplied digest alone never establishes a validated import.

The first profile uses GCC with `-x c`, `-std=gnu11`, `-m64`, `-funsigned-char`, and
`-nostdinc`. Configured include roots, forced includes, and ordered `-D` and `-U`
options select preprocessing inputs. Unsupported compiler options, response
files, plugins, and execution hooks are rejected. The compiler runs with a
cleared environment; only the configuration's supported variables are supplied.
Use explicit `SOURCE_DATE_EPOCH` when source depends on date/time macros.

Compiler invocation has output and time bounds, and failure or cancellation
stops its owned process group. Partial compiler output cannot become a
validated artifact. Dependencies come from the compiler's complete dependency
output, including configured system headers; source-map filenames are not a
substitute for that inventory.

The initial implementation snapshots the working directory, source directories,
and configured include roots before and after preprocessing. Keep them quiescent
during a load. Root/configuration/output paths with symlink components are
rejected; dependencies resolving outside the declared roots are also rejected.
Output parent directories must already exist. A project is limited to 512 MiB
and 200,000 entries in its input-root inventory, 64 MiB per artifact, 128 MiB of
combined artifacts, and 1 MiB each for its configuration and lock. Compiler
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
