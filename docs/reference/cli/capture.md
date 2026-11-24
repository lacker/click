# `click capture`

Compiler imports let a sidecar verify the C selected by a configured compiler
preprocessor. Click still parses and lowers the resulting C and independently
checks its proofs. This mode is explicit and separate from the existing bounded
source-bundle preprocessor. The same command also refreshes the preliminary
typed C++ artifact described below. [Language coverage](../coverage.md) summarizes
what the C and C++ import paths admit.

```text
usage: click capture [<project-dir> | <source>... | <sidecar.click>]
```

With no path, or a directory or `click.project.json`, the command captures
all units in the nearest project. A source path selects its configured
compilation. A sidecar selects the configured compilations named by its
`verifying` declarations, whose paths are relative to the sidecar. Proofs
can sit beside sources or in a separate tree under the project.

The manifest is `.click/captures/manifest.json`. Captures live beside it,
grouped by unit, with their source paths preserved.

Ordinary `click verify` refreshes the missing or stale captures it needs.
Use `click capture` to force a fresh capture or to produce files for later
compiler-free verification with `click verify --locked`.

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
- **A language frontend is a separate case.** Click uses the pinned
  Clang 19 exporter for C++ and Charon for Rust. They run when Click
  captures source. Verification reuses current captures offline.
- **The C++ standard library is axiomatic.** It is mostly header code that
  Clang must parse to type-check a program, so the real headers are parsed,
  but none of their code is trusted or verified: a call into a system header
  is checked against Click's contract for it. See
  [the C++ standard library](#c-standard-library).
- **The default workflow needs none of it.** `click verify` on plain C needs
  no compiler or system headers.

## Project units

A project's root `click.project.json` can declare C compiler-import units, C++
units and Rust crate units. The
project file is found from a sidecar as the nearest ancestor directory that
contains one, so sidecars may live in any subdirectory beneath it; their Click
imports stay inside the project ([imports](../../concepts/sidecars.md#local-specification-imports)).
The units' sources need not: a unit names
a source root, which may be the project directory or any external tree the user
manages (a git submodule, a sibling checkout, copied files), and Click's own
description of how its sources are built. Click reads the tree in place,
requires no layout or file names in it, and never writes into it.

```json
{
  "target": "x86_64-unknown-linux-gnu",
  "units": {
    "label": {
      "language": "c",
      "root": "../vendor/label-1.0",
      "compiler": "/usr/bin/gcc",
      "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
      "args": ["-Isrc/include", "-DLABEL_CAPACITY=32"],
      "sources": {
        "src/label_fit.c": {},
        "src/label_copy.c": {"args": ["-DCOPY_CHECKS=1"]}
      }
    }
  }
}
```

- A unit name is 1 to 64 ASCII letters, digits, `_` or `-`. `"language"` is
  `"c"`, `"c++"` or `"rust"`.
- `root` is relative to the project directory and defaults to `.`. It is the
  compiler's working directory, so `-I` paths and source keys are relative to
  it. Source keys are relative paths inside the root, without `..`.
- `compiler` is required, relative to the project directory or absolute. Plain
  C that Click preprocesses itself needs no unit.
- `env` holds the only variables the compiler runs with; every other
  variable is cleared. `option_profile` names an
  [option profile](#option-profile-linux-68-x86_64-kbuild) that admits more
  than the preprocessor flags, and a source's `projection` selects the
  [dependency-closure projection](#dependency-closure-projection).
- Unit `args` precede each source's own `args`; together they are validated
  as [Validation and supported profile](#validation-and-supported-profile)
  describes.
- The project's top-level `target` and `mode` select the C target for
  every C unit: `x86_64-unknown-linux-gnu`, the only target, in the
  `userspace` (default) or `kernel` mode; see
  [Selecting a target](../language/c.md#selecting-a-target). A unit that still names its variables `environment` is refused with the
  new name, `env`. A retired single-name target such as `x86_64-linux-kernel` is
  refused with its replacement.
- The project's top-level `optimization` is the one optimization level every
  C unit is prepared and verified for: `-O2` (default) or `-O0`. Click's
  checks cover what GCC's optimizer assumes at `-O2`, so a claim holds for
  the optimized build; see
  [Optimization level](#optimization-level). A unit argument that names
  another level, or defines `__OPTIMIZE__`, is refused.

A Rust unit is one crate or one single-file program; it takes no `compiler`,
`env`, `option_profile` or `args`, and `sources` lists exactly one
source with no arguments. Without a `crate` object the source is a lone Rust
2024 file read from its own directory, as `examples/basic-rust` does. With
one, the source is the crate root and `crate` gives the crate description (see
the [Rust reference](../rust.md#locked-crates-and-qualified-declarations)):

```json
"adler2": {
  "language": "rust",
  "root": "../vendor/adler2-2.0.1",
  "crate": {"name": "adler2", "edition": "2021", "features": ["std"],
            "roots": ["adler2::adler32_slice", "adler2::Adler32::from_checksum"],
            "files": ["src/lib.rs", "src/algo.rs"]},
  "sources": {"src/lib.rs": {}}
}
```

`roots` lists every entry point the project's sidecars verify; one extraction
serves every sidecar that verifies the crate root, and such a sidecar verifies
no other source. `click capture` runs the pinned Charon named by the
`CLICK_CHARON` environment variable, writes `.click/captures/<unit>/<crate root>.ullbc`,
and records each crate file's digest so that a changed file is refused by name.
Verification needs neither Charon nor `CLICK_CHARON`.

The Rust compiler still checks the crate. Click lowers the configured roots
and their reachable dependencies. An unsupported body in an unrelated
same-file function can stay outside this slice. A call to that function
brings its body into the slice and reports the unsupported construct at
its source location, as checked by
`charon_function_root_checks_an_unsupported_sibling_only_when_called` in
`tests/rust_import.rs`.

A C++ unit gives `exceptions` and `rtti` (both default `false`) and `args`, the
Clang arguments of its build, which Click writes into a compilation database of
its own at lock time; the standard is C++20 and the target
`x86_64-unknown-linux-gnu`. It takes no `compiler`, `env` or
`option_profile`. Each source is a logical source, a `.cpp` file or a header,
and lists the `functions` its sidecars verify; it may also give the
`translation_unit` that includes a header (by default the source itself), its
own `args`, `dependencies`, `library_assertions` and `exception_behavior`
(described [below](#preliminary-c-semantic-artifact)), and the class
`templates` it verifies once for every type argument, each named with its type
parameters, `"templates": ["Stack<T>"]`
([below](#class-templates-verified-once)):

```json
"basic": {
  "language": "c++",
  "root": "../vendor/basic",
  "args": ["-ffreestanding", "-nostdinc", "-nostdinc++", "-funsigned-char"],
  "sources": {"src/pair.cpp": {"functions": ["increment", "add_two"]}}
}
```

### C++ exporter identity

Before its first export, `click capture` runs the exporter with
`--identity`. The exporter answers with its own version, the artifact schema
it emits and its Clang version. Click compares that line with the pinned front
end in `src/languages/cpp/frontend-profile.json`, the one definition the
exporter build also reads, and refuses any other exporter with
`C++ exporter version mismatch; expected click-cpp-exporter …`. An exporter
that does not answer `--identity`, such as one built before this check, is
refused with an instruction to rebuild it.

The lock records the pinned front end, not the build that ran: its front-end
`identity` is the SHA-256 of the pinned profile, and each artifact's
`frontend_version` is the pinned `clang version 19.1.7`, however that Clang
was packaged. Every exporter that passes the handshake therefore writes the
same lock and artifacts for the same inputs, on any machine.

### C++ unit arguments

Click sets the standard, target, exception and RTTI modes, the project's
[optimization level](#optimization-level), and at an optimizing level
`-fno-strict-aliasing`, as for C. A unit's or source's `args` may not name
them, except that, as for C, they may repeat the project's level. Each other argument must be one of these, and any other is refused with
its position and text:

| Arguments | Class | Reason |
| --- | --- | --- |
| `-D`, `-U`, `-I`, `-iquote`, `-isystem`, `-include` (joined or separate value), `--sysroot`, `-nostdinc`, `-nostdinc++` | Preprocessor input | Inventoried by the lock like every file the exporter reads. A `-D` or `-U` of `__OPTIMIZE__` is refused: the level sets it. |
| `-funsigned-char`, `-fsigned-char` | Checked semantic setting | The exporter records each type's signedness as Clang resolves it. |
| `-ffreestanding` | Checked semantic setting | Removes Clang's knowledge of hosted library functions; a call still needs a declaration the exporter accepts. |
| `-g`, `-W…` (not `-Wa,`, `-Wl,`, `-Wp,`), `-w`, `-fmacro-prefix-map=…` | Diagnostics or debug information | No effect on the semantics. |
| `-fstack-protector`, `-fstack-protector-strong`, `-fstack-protector-all`, `-fstack-clash-protection`, `-fcf-protection`, `-fcf-protection=full` | Hardening code generation | Adds checks that abort only where the program already has undefined behavior, which Click refuses to prove. |

`-D_FORTIFY_SOURCE` is an ordinary define: glibc's fortified wrappers live in
system headers, and the program reaches library functions only through the
axiomatic boundary of the [C++ standard library](#c-standard-library).

`click capture` runs the pinned exporter: the one `CLICK_CPP_EXPORTER`
names, else the one installed for this Click version by
[`click add cpp`](versions.md#click-version-add)
([`CLICK_CPP_EXPORTER`](environment.md#click_cpp_exporter)). It supplies its pinned Clang's resource directory (the builtin headers such
as `<stddef.h>`; an installed exporter's `clang-resource/` beside it) to a command that names none, so `args` never states a
machine-specific `-resource-dir`. It exports every listed function of a
source into one artifact,
`.click/captures/<unit>/<source>.click-cpp.json`; a sidecar that verifies the source
sees all of them. A sidecar may verify several sources of one C++ unit, which
are linked ([calls into another translation unit](#calls-into-another-translation-unit)),
but no source of another unit. Preprocessor inputs under the
unit root or the project directory are rechecked relative to those roots;
inputs outside them, such as system, sysroot and Clang resource headers, are
pinned by the digest the lock records and are not read when loading, so the
lock verifies on another machine and after the checkout moves. The lock and
the artifact name the unit root, the project directory and the pinned Clang's
resource directory by the labels `$unit`, `$project` and `$clang-resource`,
never by the preparing checkout's path, and the import identity covers the
labelled form: preparing the project again from another checkout writes the
same lock and artifacts (`cpp_project_locks_are_portable` in
`tests/cpp_import.rs`).

A sidecar selects a unit source with an ordinary `verifying` path, relative to
the sidecar, that resolves to a file the unit lists; for example a sidecar in
`proofs/checks/` above writes `verifying "../../vendor/label-1.0/src/label_fit.c";`.
Either every `verifying` source of a sidecar is a unit source or none is. A
sidecar's own `<sidecar>.import.json`, the configuration of earlier releases,
is refused with a diagnostic naming its replacement: declare its sources as a
unit, remove the config and its lock, and run `click capture`.

The project manifest has one entry per captured unit. For C, the
captures live at `.click/captures/<unit>/<source>.i`. Keep the manifest
and output together to verify without the toolchain. Every language's entry has one shape:

```json
{
  "envelope": 1,
  "unit": "<SHA-256 of the unit's description>",
  "frontend": {"name": "gcc", "identity": "<SHA-256 pinning the front end>"},
  "sources": {
    "src/label.c": {
      "inputs": {"src/label.c": "<SHA-256>", "$unit/include/label.h": "<SHA-256>"},
      "artifact": {"path": ".click/captures/main/src/label.c.i", "sha256": "<SHA-256>", "bytes": 1234},
      "identity": "<SHA-256>"
    }
  },
  "c": {"target": "x86_64-unknown-linux-gnu", "...": "..."}
}
```

`sources` is keyed by logical source. `inputs` are the digests of the files the
source was prepared from, `artifact` the prepared output, and the one section
named for the unit's language (`c`, `c++` or `rust`) holds what only that
language records. A source's `identity` is the SHA-256 of all of it: the
envelope schema, the language, the unit digest, the front end, the source's
inputs and artifact, and the whole language section, so a change to any
recorded field changes it. It is the import identity proofs and caches key on.
An entry without `envelope`, written by an earlier release, is refused with
``run `click capture` to prepare it again``. Editing the description or
the project target refuses the lock until it is prepared again.
Loading rechecks the unit's sources and every header the compiler opened under
the project directory or the unit root, so the lock still loads after the whole
checkout moves, and a changed input is refused with the file named. The lock
names those roots `$project` and `$unit` rather than by the preparing
checkout's path, and its front-end and source identities cover that form, so
preparing the project at another path writes the same lock
(`compiler_import_project_locks_are_portable` in `tests/compiler_import.rs`).
The selected compiler and its backend are named by path and pinned by digest.

## The prepared state

Verification loads a unit's recorded artifacts without executing or locating
its compiler or front end. The artifacts and lock move with the project: loading
checks their hashes, the artifact bytes and size, the target, the recorded
toolchain and front-end identity, and each source's import identity. System
headers used during preparation are identified in the lock but need not be
installed on the verification host. A C unit's sources and project-local
headers are rechecked in the unit root, so a changed one is refused by name.

This verifies the **prepared state**. A change to the C source or an opened
project-local header is rejected during loading. A change to external headers,
or the appearance of a previously absent header selected by `__has_include`,
does not silently change that state; run `click capture` in the selected
toolchain environment to prepare a new one. The lock is a consistency record,
so publication and origin of a native platform artifact still need a
trusted preparation process.

Lock creation is source preparation, not proof verification. The C parser can
still reject an unsupported construct when a proof tool loads the prepared
translation unit. No C declarations, function bodies, storage, attributes, or
assembly are silently deleted to make an import pass.

## Preliminary C++ semantic artifact

The preliminary C++ frontend boundary accepts one C++20 translation unit
selected by exactly one entry in a JSON compilation database, with one
selected free function or ordinary method and the uniquely named definitions
reachable from its supported direct call statements.
An unrelated same-file body can use statements outside the supported slice.
A call from a selected function brings the callee into the exporter, which
reports unsupported statements at their source location. See
`cpp_function_root_checks_an_unsupported_sibling_only_when_called` in
`tests/cpp_import.rs`.

In the baseline profile, exceptions are disabled and every selected or
reachable function must declare `noexcept`. A second, deliberately smaller
profile may retain the compilation
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

A C++ unit's baseline profile is C++20 for `x86_64-unknown-linux-gnu` with
exceptions and RTTI off; each source names its logical source, its `.cpp`
translation unit when that differs, and the functions to export. `exceptions`
and `rtti` may also be true for a supported normal-only reachable graph; the
observed Clang profile must match the unit.
`click capture` executes the repository-owned Clang 19.1.7
LibTooling exporter with the command Click synthesizes and records the database bytes, exact parsed
command and directory, source, explicitly declared reachable-declaration
dependencies, every file Clang lexes while preprocessing the translation unit,
exporter, semantic profile, artifact, and configuration identities. Reachable
declaration spans outside the logical source must name one of the relative
dependencies. The broader preprocessor inventory also covers headers whose
declarations are not lowered. For each opened file the lock records its
accessed path, resolved target, and content hash. Refresh repeats the export
across a bounded inventory state; offline loading rejects changed contents
or symlink targets without running Clang.
The unit root is also the dependency root: it may contain the project source
tree and a Linux sysroot. Dependencies retain paths relative to that root. The
Bitcoin Core integration in `integrations/bitcoin-core-money-range/` uses this
arrangement, with the real CMake command's arguments as the unit's `args`.

The synthesized command uses the pinned Clang driver and the unit's C++20,
target, exception, and RTTI profile. Missing or ambiguous entries and mismatched driver
or semantic profiles fail refresh locally. When `logical_source` names a
header, the importer resolves and hashes that file separately from the `.cpp`
translation unit. Offline loading rejects a missing or modified selected
header. Textually included project, sysroot, and Clang resource headers are
inventoried even when they lie outside the configured dependency root.
Response files, PCH, modules, VFS overlays, and arbitrary Clang pass-through
options are rejected because their hidden inputs are not inventoried.

For a compilation command with exceptions enabled, the unit instead sets
`"exceptions": true`; the observed Clang profile must agree. The semantic
artifact records `exception_behavior: "normal_only"` independently from each
function's `declared_noexcept` value. This is not exception handling support:
reachable `throw`, `try`/`catch`, unresolved calls, and local object construction
are rejected locally. Borrowed references to the supported trivially destructible
record may use its checked fields and ordinary methods. Because the artifact contains the complete supported
direct-call closure and has no throwing operation, ordinary verification may
check its normal behavior without inventing an exceptional proof outcome.
An RTTI-enabled profile also permits those borrowed records; this does not add
`typeid` or `dynamic_cast` semantics.

A source may instead select `"exception_behavior": "ios_failure"`, with
`"exceptions": true`, for propagation of an opaque
`std::ios_base::failure`. It accepts the exact external narrow-string
constructor with its default `std::error_code` argument, using an ordinary
nonzero ASCII string literal of at most 4096 bytes. Configure a
`library_assertions` entry with `kind: "opaque_exception_constructor"`,
`function: "std::ios_base::failure::failure"`, and the declaration header's
relative `header` and `sha256`. The artifact records the resolved constructor,
canonical declaration file, literal and source span; loading checks them
against that configured pin and the locked input closure.

The constructor model returns a fresh opaque value, with no observable memory
effects. Exception storage and destruction belong to the C++ runtime.
**This profile assumes allocation failure terminates**, as with Bitcoin's
installed new-handler; it does not model propagation of `std::bad_alloc`
([trust](../../concepts/trust.md#library-interfaces)). Direct `throws` contracts
may borrow memory with `owns` and `views`, and must establish their footprint
and exceptional guarantees after a throw. The pinned `SpanReader::ignore`
fixture verifies the real `streams.h` through this boundary. Nontrivial
opaque-exception unwinding, typed class catches, base-class matching,
rethrow, message inspection and general class exceptions remain refused.
The existing `normal_only` and `scalar_int32` profiles retain their rules.

A source may select `"exception_behavior": "typed"`, with `"exceptions": true`,
for ordinary user-defined exception aggregates. `throw Error{code}` constructs
an opaque value of that exact imported class; `throws Error` (including a
qualified name such as `errors::ParseError`) names it in the sidecar. The
class must be a trivially copyable aggregate with trivial destruction, no
bases, and supported scalar fields. Empty tags such as `struct End {};` are
also supported. Every field must have an explicit initializer; its reads and
arithmetic definedness are checked in source order even though the payload
fields cannot be inspected. Construction and copying need no user-constructor
axiom. Scalar `int32` throws also work in this profile. A pinned
`std::ios_base::failure` construction still requires its library assertion.
User exception constructors, lvalue throws, nontrivial exception objects, class catches
and rethrow remain refused.

Exception-enabled profiles also admit user `noexcept` definitions, including
`noexcept(true)`, ordinary methods and supported constructors/destructors.
Their sidecars omit `throws`: the imported declaration requires a nonthrowing
contract, and the ordinary body proof must establish that no exception escapes.
The declaration is not an assumption that a throwing body is safe. The
exporter defers Clang's specific explicit-throw-in-noexcept warning to this
proof check; other compiler diagnostics retain their admission policy. A call to
a potentially throwing function is valid when the caller's preconditions and
the callee's exceptional guarantees exclude that outcome. Scalar exceptions
caught inside a `noexcept` function may also be verified. `noexcept(false)`
retains the ordinary potentially throwing interface. No additional sidecar
syntax is needed.

Normal cleanup stays checked in `noexcept` functions. `typed` and
`ios_failure` still refuse potentially throwing functions with automatic
destruction; general class unwinding and `std::terminate` paths are not
modeled. An escaping exception remains a proof refusal, even if a sidecar
tries to admit it with `throws`.

A source's separate `"exception_behavior": "scalar_int32"` requires
`"exceptions": true`. Its locked artifact may contain a source `throw` of a
typed `int` payload in an object-free function; the importer lowers that node
to Click's checked exceptional statement outcome. The contract uses
`throws int32` when it permits an escaping exception; a nonthrowing contract
must prove that outcome unreachable. Normal and exceptional postconditions
are proved separately. Reachable direct calls can propagate that exception
while normal scalar statements continue. One object-free
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
from a guarded `try`, and consuming or producing exceptional resources. This is not general
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
}
```

`owns value` owns the referent, `value` reads it, and `&value` is its address,
for a contract that says two references alias (`requires &a == &b;`) or that a
stored pointer points at one. A struct reference names its fields as
`state.field`. Writing `int32* value` for an `int&` is a signature mismatch
that names both types; a C++ `int*` parameter stays a pointer. A member
function's receiver is the pointer `this`, as in C++: `this->fee`,
`owns *this`.

A pointer to a simple record, `Node*`, is a parameter, a local, a field and a
result, its value the record's address or null. `p->field` reads and writes
the record when `p` is a parameter or local. An arrow through a field or a
call result, `p->next->value`, is refused. `nullptr` initializes and assigns
one, and `==` and `!=` compare two of one record type. The sidecar writes the
type as the source does, in a head and in a specification's binder: a
resource over `p: Node*` describes a list by its nodes
(`mdtests/cpp_record_pointers.md`). A pointer to a polymorphic class is
refused.

`target = new Node{v, n};` allocates one such record with the global
`operator new`, its brace initializer naming one value per field in
declaration order, and assigns its address to a local or field. It is
admitted in a `noexcept` function: a failed allocation throws
`std::bad_alloc`, which there ends the program, so the result is never null
and the caller holds `allocation(p, sizeof(Node))` and `*p`, as after a
successful `malloc`. A contract writes `sizeof(Node)` for the record's size
and `aligned(p, 8)` where a callee needs the pointer's alignment. `delete p;`
ends a record with trivial destruction through the global `operator delete`,
needing the same resources as `free`; deleting null does nothing
(`mdtests/cpp_new_delete.md`). Array `new` and `delete[]`, placement `new`,
class-specific allocation functions and `new` in a declaration are refused.

A field may have a constant default member initializer, `Node* head =
nullptr;` or `unsigned long count = 0;`. A local built by the record's implicit
or defaulted default constructor, `Stack<int> stack;`, where every field has
one, is initialized from them in declaration order, as the constructor does.
Such a record may have its own written `noexcept` destructor, which runs at
each of the local's scope exits as a constructed object's does: `~Stack()`
deletes the remaining nodes in a `while` loop, and its sidecar contract
consumes the list (`Stack<int>::~Stack() { owns *this; consumes list:
nodes(this->head); }`). A class template's destructor is verified once for
every `T` as its methods are, `template<class T> Stack<T>::~Stack() { ... }`,
each instance's destructor taking that contract. A call made while such an
object lives runs inside its unwind cleanup; a `noexcept` callee's call still
has one successor, so `step()`, `step_until`, and the implicit tail pass it
as any call.
A scalar local may be passed for a native reference parameter, `int out = 0;
stack.pop(out);`: the callee receives its address. These and record pointers
and `new` verify the class template `Stack<T>` at its `int` instance
(`examples/cpp-stack/`), and once for every `T`
([`mdtests/cpp_generic_resource_checked_once.md`](https://github.com/clicklang/click/blob/master/mdtests/cpp_generic_resource_checked_once.md)).

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
in the sidecar. A C++ sidecar may also write `std::byte` itself, in a head,
contract or `sizeof`: it is `uint8`, and `const std::byte` is `const uint8`. They are admitted as parameters, results and locals. A call
that returns one can also be read or written directly, as in `return s[0];`
and `s[0] = v;`. A read is a typed load of the returned address and needs a
resource for the referent. A write needs a mutable referent and owns it; its
value must be free of calls and is read before the call, as C++17 sequences
an assignment's right operand first. Compound assignment through a returned
reference remains unsupported. Ending the local binding does
not end the backing object's lifetime. Scalar references to local objects,
temporary lifetime extension, rvalue references and nested reference
declarations remain unsupported.

Struct/class reference locals also bind existing objects: a record reference
parameter or alias, a local record object, a nested record member, or a
record-pointer dereference. `auto&` and `const auto&` retain Clang's resolved
record identity and const qualification. A proof reads `ref.field` and names
its address as `&ref`; the alias grants no memory permissions. Writes through
a mutable alias need ownership, and const aliases continue to observe writes
through a separately authorized mutable alias. Ending a reference binding does
not destroy its backing object. Pointer-based binding checks the complete
record's live byte footprint without reading or initializing its fields.

Struct/class lvalue-reference results use `Widget&` or `const Widget&` in
sidecar heads. `result.field` reads the returned record and `&result` names
its address. Functions may return an existing reference or supported object
lvalue, a nested record member, a record-pointer dereference, or forward a
matching reference-result call. Reference locals bind matching direct call
results as well as existing object lvalues. These calls preserve record
identity, const qualification, subobject bounds and backing authority; the
returned address grants no ownership or initialization. A dangling address
under an alias-only claim does not promise live backing; later accesses still
check storage lifetime and permissions.

A direct integer field read such as `return outer.get().value;` uses the
expression observer rules, including a nonthrowing getter with a read-only
contract. A simple assignment such as `outer.get().value = outer.first;`
evaluates the right operand before calling the getter. The store requires
writable authority for the selected field and a mutable record reference.
Both forms evaluate the getter once. Compound assignments with `+=` and
`-=` also support direct same-width signed integer fields on a returned
record reference. Click reads the selected field after the call, checks
signed overflow, and stores through the same returned reference. Rvalue
references and temporary lifetime extension remain outside this slice.

A record-reference name shared with a
different record layout or a non-reference object in another scope is refused,
rather than assigning its proof fields an ambiguous layout.

A proof names a reference local as it names a reference parameter. For
`int& r = value;`, `r` is the referent, as in `have r == 1;`, and `&r` is its
address, as in `have &r == &value;`. `r[0]` is refused with the form to
write. Binding a reference is not an assignment, so `assignment(r, N)` is
refused; a store through `r` is selected by its statement.

A reference argument bound to a native scalar field keeps that field's selected
bounds, matching the complete pointer value of `&object.field` in a contract.
An access beyond the member remains invalid even when a sibling field is also
available. See the checked
[member-reference equality](https://github.com/clicklang/click/blob/master/mdtests/cpp_a_member_reference_parameter_retains_its_member_equality.md)
and [sibling-access refusal](https://github.com/clicklang/click/blob/master/mdtests/cpp_a_member_reference_parameter_keeps_its_subobject.md).

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
`int*`, `unsigned int*` or `unsigned char*` (also pointers to const elements), one `const` signed-64 reference, and mutable or const references
to supported simple record types with distinct proof-facing names. Selected functions return `int`,
signed/unsigned 64/128-bit integers, `unsigned int`, `unsigned char`, `bool`, mutable `int*`, `unsigned int*` or `unsigned char*`,
native element references, supported record references, or `void`.

Free and ordinary member functions also admit mutable by-value simple-record
parameters with trivial copying and destruction, without base subobjects.
Clang-resolved trivial copy arguments retain a distinct `record_copy` artifact
node, nominal type, lvalue projection, and span. The shared aggregate model
copies the descriptor into separately owned parameter storage; pointer fields
keep their original backing allocation and do not grant access to it. Moves,
prvalue arguments, user-defined copy bodies, and nontrivial destruction remain
refused. Artifact schema 57 requires refreshing older locks.

For a direct nonthrowing statement call or a direct call supplying a scalar
initializer or return, an opaque trivial copy constructor can initialize the
by-value parameter through its Click contract. The constructor's destination
and the callee's parameter are the same private object. The call can select the
constructor's produced resource using its parameter's address, with no raw
field reads or new authority over backing memory. Logical resources keyed by
the parameter's address must be discharged by the end of the full expression,
such as through a callee's `consumes` clause. Click then retires the parameter's
storage. Refresh an existing import lock to retain this constructor call.

Contracts cannot observe a modified private parameter object as though it were
the caller's original object. Entry-state pointer values can still name
backing effects: `load<int32>(old(value.data))` reads current memory through the
entry pointer, while `old(load<int32>(value.data))` reads entry memory.

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
    ensures result == (if old(nValue) >= 0i64 { true } else { false });
} by {
    if nValue >= 0i64 {
        step_until(function.exit);
        close();
    } else {
        step_until(function.exit);
        close();
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
Implicit calls on `this` retain the existing checked receiver interface; virtual
dispatch remains outside the slice. Lowering captures the result in a
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

A function-pointer parameter is a callback, as in C. Its type is a pointer to a
`noexcept`, non-variadic function whose parameters and result are bools,
supported integers or mutable native element pointers, `int (*f)(int) noexcept`;
a pointer to a function that may throw is refused, since a call through it would
need an exceptional contract. A call through it, `f(x)` or `(*f)(x)`, is a
`through_pointer` callee in the artifact naming the variable, and lowers to the
kernel's indirect call, so the sidecar's `requires Doubling(f)` supplies its
contract exactly as for C. The call may be a statement, a local's initializer or
a returned value, with value arguments and no nested call. `&f`, or `f` decayed
to a pointer, passed for such a parameter is a `function_address` value: the
importer exports `f` and checks that it is a `noexcept` free or static member
function of exactly the pointer's type, and the caller's proof shows that `f`
meets the required contract, from `f`'s own contract or an `executes` theorem.
A function-pointer local, `int (*g)(int) noexcept = f;` or `= &twice;`, is
initialized once with `&f` or another pointer of the same type, and calls go
through it as through a parameter. A parameter or local passed on as it is to
a function-pointer parameter of the same type is a `load` argument, so a
function that forwards a pointer requires the contract its callee requires.
Reassigning a pointer, storing one in memory, and any other read of its value
are refused (`tests/cpp_import.rs`, `*function_pointer*`).

A lambda that captures nothing, passed for such a parameter,
`apply([](int y) noexcept { return y + y; }, x)`, is its call operator's
address: the importer reads Clang's conversion of the closure to the pointer
type as a `function_address` of the call operator, which it exports as a free
function of the lambda's parameters. The sidecar names it by its enclosing
function and its index among the lambdas written in that function's body, in
source order: `int caller::(lambda#0)(int y) { ... } by { ... }`. A lambda in a member function, a capturing or
generic lambda, and a lambda used other than converted to a function pointer
are refused (`mdtests/cpp_lambda_named_contract.md`,
`tests/cpp_import.rs`, `cpp_lambdas_*`).

A `std::function<R(A...)>` parameter, by value or by `const` reference, is a
callable value of its signature, as a function pointer is; the sidecar head
writes it as the source does, `int apply(const std::function<int(int)>& f,
int x)`. Click models it as the callable it holds, never the library's
record, so its layout is not read, and a contract on it, `requires
Doubling(f)`, implies it is not empty: a call through it cannot throw
`std::bad_function_call`. `f(x)` is a call through the value. The exporter
reads the construction of a `std::function` argument from what it is made
of: a function is its address; another `std::function` parameter or local
is a load of the callable it holds; and a lambda is made from the values it
captures by copy, a closure creation the importer evaluates before the call
into a fresh local, by the lambda's instance function. The lambda's call
operator is exported with its captures as leading parameters, named for the
captured variables, and its sidecar contract reads them by name,
`int caller::(lambda#0)(int y) { requires 0 <= k and k <= 1000; ensures
result == y + k; }`. A callee requiring a parameterized contract of the
value, `requires Adds(f, { amount: k })`, is met by refinement from the
lambda's contract fixed to its captured values, as for a Rust closure (see
[Rust closures](../rust.md#function-pointers-and-named-contracts)). A
capture by reference is refused, since C++ does not keep the variable from
changing while the closure lives, and so are captures of non-scalars,
`std::function` locals, and calls through a `std::function` that is not a
parameter or local (`tests/libcxx_functional.rs`, against the pinned closure
in `tests/fixtures/libcxx-functional`).

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
Reference reads, dereferences, arithmetic and side effects in siblings
remain outside this ordinary nested-call rule.

An argument list can also contain several direct, nonvirtual
`const noexcept` getters with no explicit parameters, as in
`sink(dst.data(), src.data(), dst.size())`. Each getter must have a checked
read-only, terminating contract. The argument types must match the getter results and
any other arguments must be stable scalars. The same rule permits a
projected receiver in a call such as `cursor.remaining.subspan(dst.size())`.
Click evaluates each getter once in argument order after establishing
that the evaluations are read-only and nonthrowing. The surrounding
function may itself throw.

An omitted argument of a supported integer type can come from a direct,
non-`constexpr`, `noexcept` helper with no arguments, such as `limit()` for
`int limit(int n = default_limit())`. The helper follows the ordinary
nested-call sequencing checks and runs once before `limit` is entered.
The import tracks the source supplying the default and records the nested
call at the omission site. An explicit argument uses the ordinary call path.
Integral constant defaults continue to use Clang's evaluated value.

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
kernel's ordinary `Declare`, `CallResult`, and `Assign` statements. The call
retains its result before a separate assignment updates the local; both program
points can be named in proofs. Construction-return calls instead use
`CallConstruct` to initialize the supplied destination directly, without a copy.
Later reads and assignments use the existing scalar rules. This makes call results usable
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

Native pointer parameters, local aliases, returned pointers and callback
signatures retain pointee const qualification. `const int*`, `const unsigned
int*` and `const unsigned char*` use `const int32*`, `const uint32*` and
`const uint8*` sidecar types. Reads require `views` or `owns`; const does not
create permission or freeze a mutable alias. Implicit qualification and
`static_cast<const T*>(p)` add const without changing the address or native
element type, including converted call results. Null returns retain the
same qualification. Source and artifact checks refuse const removal,
mutable sidecar substitutions and stores through const pointers. Volatile
pointees, other character types and top-level const pointer variables remain
outside this profile.

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
The proof interface writes that reference as `struct Name*` and uses ordinary
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
an unwritten declared uint32, while partial stores cannot. Output transfer
also composes with this view: a body-checked helper that consumes
four unwritten bytes and produces them initialized can specify each output byte;
the caller can prove the exact little-endian uint32 when reading its declared
object. Builtin native scalar pointer subscripts `p[i]` and `i[p]` with 32/64-bit
integer indices use the same checked pointer-add/load/store forms as `*(p + i)`.

Native contract casts such as `result == p as (uint8 *)` express pointer identity across access
types without granting authority. Dynamic-extent `std::span<std::byte>` now
retains authenticated standard-byte template arguments, including their
positions and locked declaration metadata even when fields do not mention
the enum. Other enum template arguments remain refused. A class template
also takes `unsigned char` as a type argument, as in `std::span<unsigned char>`;
integral template values remain 32/64-bit. The library contract
for dynamic-extent `std::as_writable_bytes(std::span<int>)` and
`std::as_writable_bytes(std::span<unsigned int>)` preserves the backing address and
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
`"function": "FeeFrac::operator+="` (or `operator-=`).

A C++ sidecar writes each head as C++ declares the function:
`bool FeeFrac::IsEmpty() const`, `void FeeFrac::operator+=(const FeeFrac& other)`,
`Restore::Restore(int* slot)`, `Restore::~Restore()`, a static member as
`static int64 FeeFrac::Div(int128 n, int32 d, bool round_down)`, and a function
template instance as `choose<true>(int a, int b)`. A record is named by its own
name, without `struct`. A member function's receiver `this` is implicit, and
the head's trailing `const` makes it `const FeeFrac* this`; a contract clause
names it `this`. Const record reference parameters retain the same
qualification. This restricts writes through that parameter without
forbidding an alias through a mutable parameter. Diagnostics, claim labels and proof steps name the function as the head
does: `FeeFrac::IsEmpty`, `FeeFrac::operator+=`, `Restore::Restore`,
`choose<true>`. A member of a class template instance is written with the
instance as Clang prints it against its template's parameters, which
leaves out trailing arguments equal to their defaults and integer
suffixes: `Stored<long long>::Stored(int64 next)`,
`int32 Box<SizeTag, true>::Read() const`, `std::span<int>::size`,
`std::span<int, 4>::size`;
so are `extern` and named-contract heads, a proof step's callee,
`step(FeeFrac::IsEmpty)`, the target of an
`executes` theorem, and a function's address, `&FeeFrac::EvaluateFeeDown`.
The importer names each function by its C++ path, which the artifact
records, as the Rust importer names an item by its path: `__cpp_q` and each
segment with its length, an identifier as written and any other segment,
such as `operator+=`, `~Restore` or `Stored<long long>`, as its bytes in hex.
The encoding is self-delimiting, so a diagnostic decodes it without the
import; a claim argument may name a label either way. A free function with
a one-word path keeps that name. An artifact locked before paths were
exported is refused with a request to run `click capture` again. Direct nonvirtual `operator[]`
methods also use this method-call path, with `Class::operator[]` both as the
selector and as the head's declarator. The receiver must be a live record lvalue; argument and result types,
const qualification and reference authority follow the ordinary method rules.
This does not admit other overloaded operators or temporary receivers.

Unused member functions, constructors, templates, and nested declarations are
not imported into the execution graph. Reachable definitions and the record's
complete supported field layout are still checked. Overloaded proof names and
reachable unsupported bodies fail import.

Direct `object.method(...)`, explicit `operator+=`/`operator-=`, and
`object += other`/`object -= other` calls bind that receiver to the selected declaration identity. Call arguments
must be direct supported references or the existing value arguments; pointer
receivers other than `this`, other overloaded operators, and call results
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
type-alias origins and cycles throughout both branch arms, scopes, handlers,
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

C++ calls and contracts bind through Clang declaration IDs, named by their
C++ paths, `A::Nested::echo` or `(anonymous namespace)::same`. If reachable
declarations share a path, as overloads do, each contract name is
`__click_cpp_decl_` plus the full lowercase hexadecimal UTF-8 declaration ID
from the artifact. This prefix is reserved: a source declaration beginning
with it also receives an encoded name. The lowered-import API exposes
`contract_name(declaration_id)`.
Reachable overloads are supported. A head at their shared path selects the
overload whose receiver constness and parameter types it writes,
`int& Box::get()` or `const int& Box::get() const`; a head that matches none,
or more than one, is refused. Selecting an overloaded declaration as a
`click verify` target, a proof step's callee or an address still fails.

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
aliases preserve their origin without changing the value kind. Reference and
record-field restrictions remain specific to their positions in the profile.
Explicit integral casts use one C++ conversion policy over the common kernel;
the frontend does not re-infer promotions from source syntax.

The `signed-arithmetic` fixture lowers signed 32/64-bit `+`, `-`, `*`, `/`,
`%`, unary negation, and `==`, `!=`, `<`, `>`, `<=`, `>=` into the common checked
kernel. Clang's integral promotions and signed casts are explicit artifact
nodes; mixed-width operands require those conversions. Signed 64-to-32
narrowing follows C++20's modulo semantics using the kernel's unsigned bit
conversion and signed reinterpretation. Boolean conversion preserves the
nonzero meaning of all 64 bits: a C++ `bool` is Click's logical `Bool`, a
conversion to it is the test `x != 0`, and a `bool` promoted to an integer is
its value `b as int32`, 1 when it holds and 0 otherwise. Division truncates towards zero, and remainder
has the dividend's sign. Zero divisors and the `MIN / -1` and `MIN % -1`
overflow pair fail verification. Addition, subtraction, multiplication, and
negation retain their signed-overflow obligations. Scalar local call initializers
also accept an ordered chain of Clang-resolved integral and Boolean conversions,
including explicit same-type alias casts. Each conversion retains its exact
cast kind, explicit/implicit origin, source and result types, alias origin,
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
model, including argument stability and compiler-`known` checks. C++
narrowing list initialization remains a compiler error; empty lists,
unsupported scalar widths, and unsupported effects remain refused. This
normalization adds no artifact node or schema version.

On a normal wide multiplication path, after both native range guards hold,
the shared kernel certifies the result's mathematical observation as the
exact Integer product. Pure Integer observation and capture retain the native
guards but do not demand that a certified result definition be supplied as
another assumption. False product claims and missing guards remain refused.

The `wide-contracts` fixture adds by-value wide parameters, results, and
matching-width call captures. Contracts write these types as `int128` and
`uint128`; `to_integer(value)` observes their full mathematical value.
`to_int128(z)` and `to_uint128(z)` require both exact destination bounds;
these proof conversions remain distinct from C++ modulo casts. Identities,
cast round trips, full signed/unsigned endpoints, modular calls with framed
narrow memory, expansion, and retained audit have regression coverage.
Bounded `close()` recognizes direct observer equalities; it does not currently
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
ordinary arithmetic proof consumes two named constant-endpoint bounds on the
source observation, checking both against the destination range. Both signed
and unsigned 128-bit values narrow to signed/unsigned 32/64-bit results.
The rule also checks native quotient/remainder narrowing under their existing
definedness guards and stated result bounds. Out-of-range casts still wrap;
missing range premises, false results, and undefined operands are refused.
Modular caller framing, offline loading, expansion, and retained audit have
coverage. This adds proof support without changing the schema or trusting
conversion bounds. See [Integer cast identities](../../internals/mathematical-integers.md#range-checked-modulo-cast-identities).

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
A sidecar names an instance as Clang prints it, `choose<true>`,
`identity<unsigned long>` or `Value::select<false>`; type aliases print as
their canonical type, and equal-width types such as `long` and `long long`
remain distinct. Callable name collisions use the existing injective
Clang-declaration identity names.

Concrete class-template instances reached through ordinary selected callers
are written as Clang prints them, including
named empty trivial tag types declared in the locked import root:
`Box<int, false>` and `Box<SizeTag, true>`. A type in a head or clause
writes a record by its C++ path, `Box<int, false>&`, `ns::Rec*` or
`std::span<int>&`, or by the layout name the importer records,
`struct Box__int__bool_false`, from ordered builtin/Boolean argument tokens
and `__tag_Name` for a tag type. Diagnostics print the C++ path,
`Box<int, false>`, for a layout name.
Qualified tag names include their namespace components. Clang's canonical USR
keeps each record, field and method nominally distinct even when layouts match;
aliases share the canonical instance. Method, constructor and destructor names
use the concrete record name. Record-name collisions are import errors. At most
32 class arguments are supported. Clang completes reachable specializations
before layout export, including unused reference parameter types.
Instances with a layout must satisfy
the ordinary record and executable-body profile, including the bounded single-base layout profile below, supported fields and
destruction, and no virtual dispatch. Empty tags serve only as type arguments;
this does not add empty runtime objects. Click verifies the
resolved layout and bodies without performing template substitution itself.

### Layout-free class addresses

References and mutable pointer parameters to named forward-declared classes
can be passed to contracted calls. The C++ artifact retains the class's
nominal declaration. A reference also retains its constness. These addresses
carry no access to object bytes. Field projections,
by-value operations, and automatic storage require a modeled layout.

The catalog can select this boundary for a complete system class as well. An
existing `const std::vector<unsigned char>&` can call `size()`, `empty()`,
`data()`, and bounded `operator[]` under Click contracts that read a
`vector_state` resource keyed by the receiver. The
[vector reference](../library/index.md#stdvectorunsigned-char) shows how
a caller supplies backing bytes when it passes a span to a reader.
The importer retains the class and method identities from Clang. The artifact
contains no allocator layout, object fields, or library body
(`tests/cpp_import.rs::byte_vector_size_uses_a_layout_free_catalog_contract`).

### Class templates verified once

A class template a source lists in `templates`, `Cell<T>`, is also exported at
an abstract type argument for each of its type parameters: a record that
the exporter declares ahead of the translation unit and prints as the
parameter's name, whose size Click reads as `sizeof(T)`. A written method of an instance a caller
reaches, `Cell<int>::set`, is exported with its signature only and the method
it is an instance of, `Cell<T>::set`, whose body is exported at the abstract
argument. In that body a value of `T` is a value of the type parameter `T`:
it is passed, returned, copied into locals and fields, and read and written
through `T&`, and nothing else. A sidecar states and proves the generic method
once, with `T` an abstract type in its head, contract and proof:

```text
template<class T> void Cell<T>::set(T v) {
    owns *this;
    ensures this->value == v;
}
```

Each instance has that contract at its types, written out from the generic
block and read at the instance's own Clang layout: `Cell<int>`'s `value` is a
4-byte `int`, `Cell<T>`'s `sizeof(T)` bytes. The sidecar does not write an instance's
contract; `void Cell<int>::set(int v) { ... }` is refused. An instance's
parameters take the instance's own names, by position: if Clang names
`Cell<int>::set`'s parameter `value`, the written-out contract reads `value`
where the template wrote `v`, so a template need not write an implementation's
reserved names (libstdc++'s `__count`). A non-template head restates its one
declaration and keeps its names exactly.

A value of `T` takes `sizeof(T)` bytes, a size Click does not know, so a
record holding one, `Node<T>`, has a symbolic layout. Its fields before the
first that depends on `T` (a `T` value or an embedded record that holds
one) keep their fixed ABI offsets, after the vtable pointer of a polymorphic
class; that field and each after it lie at `offsetof(Node<T>, value)`, and
the record's size is `sizeof(Node<T>)`, terms that are each instance's own
numbers. Two fields of one object are apart by the layout, whatever their
offsets, and each lies inside the object's `sizeof(Node<T>)` bytes. So
`*p` for a `Node<T>* p` is `p[0u64..sizeof(Node<T>)]`, `new Node<T>`
allocates `sizeof(Node<T>)` bytes, `owns allocation(p, sizeof(Node<T>))`
states that allocation, and a `T&` parameter owns `sizeof(T)` bytes. A claim
that a size is one number, `sizeof(Pair<T>) == 16`, does not hold for every
`T` and fails
([`mdtests/cpp_class_template_size_depends_on_its_arguments.md`](https://github.com/clicklang/click/blob/master/mdtests/cpp_class_template_size_depends_on_its_arguments.md)).

A resource takes type parameters as a method does, `resource nodes<T>(p:
Node<T>*) { field items: List<T>; ... }`, and each use names its arguments,
`nodes<T>(this->head)` in a generic method and `nodes<int>(stack.head)` in a
caller. The sidecar writes the resource out at its own parameters, checked
once for every `T`, and at each argument list a use names, the written
instance methods' included, each laid out at its types. A generic spec
function, `function length<T>(xs: List<T>) -> Integer`, may compute with
Integer, and a contract or proof unfolds it at a list of abstract values
([`mdtests/cpp_generic_resource_checked_once.md`](https://github.com/clicklang/click/blob/master/mdtests/cpp_generic_resource_checked_once.md)).
A method that reads a value of `T` out of a node the resource owns, as the
stack's `pop` does, is proved once too: a read of a node's `T` field whose
bytes no store changed since the resource stated its value is that value,
whether the read is the C body's (`out = node->value`) or a `fold`'s
(`fact p->value == value` at a later point).

The exporter keeps the body the same at every type argument. It refuses a
listed template, or a template its generic bodies use at abstract arguments,
`Node<T>`, that has an explicit or partial specialization, or an explicitly
specialized member; a generic body whose template pattern has `if constexpr`,
a size, alignment, type trait or `noexcept` test of a template argument, a name
in a template argument's scope, a cast or conversion involving a template
argument, a concept or `requires` test, or a static data member of a template;
and a value of `T` passed to anything but a method of a template at abstract
arguments, which could be another overload or specialization at each type. A
listed template takes exactly the type parameters it is named with, without
defaults, packs or non-type parameters, and its written constructors are
outside the slice.

A sidecar template also takes a non-type parameter, an extent written
`std::size_t N`, `size_t N` or `unsigned long N`:
`template<class T, std::size_t N> unsigned long Buf<T, N>::size() const {
ensures result == N; }`. Each instance writes the extent as a `uint64`
literal in its contract, `4u64`, and as Clang prints it in its path,
`Buf<int, 4>::size`. The exporter does not yet export a template with a
non-type parameter at abstract arguments, so only the Click library's
templates, whose instances are imported axioms, are written out this way
today (`std::span<T, N>`, `std::array<T, N>`). An
instance's type arguments are the scalars of a concrete instance above
([`mdtests/cpp_class_template_verified_once.md`](https://github.com/clicklang/click/blob/master/mdtests/cpp_class_template_verified_once.md)).

A method with a `const` and a mutable overload, `T& get()` and `const T&
get() const`, is two template methods at one path, each stated once. A head
at a path that overloads share names the overload whose receiver constness
and parameter types it writes, as any C++ head does, and each instance is
written out from the template method whose head has its receiver's
constness: `Cell<int>::get` called through a `const` reference from `const T&
Cell<T>::get() const`
([`mdtests/cpp_class_template_const_overloads.md`](https://github.com/clicklang/click/blob/master/mdtests/cpp_class_template_const_overloads.md)).
Overloads of a template method that differ otherwise are refused.

A `do { ... } while (false)` or `do { ... } while (0)` wrapper executes its checked body
once through the shared conditional model. Only literal false conditions are
admitted for `do`; break/continue and nested automatic locals in it remain
refused. This admits the wrapper shape used by assertion macros without
assuming their bodies or conditions.

A `while (condition) { ... }` loop lowers to the kernel's loop, and the
sidecar proves it with the `loop { ... }` tactic as for C. The condition is an
expression evaluated before each iteration, not a call; the body may declare
scalar and pointer locals, which live for one iteration, and may return. A
condition variable, `break`, `continue`, a record object declared in the body
and `for` loops are refused
([`mdtests/cpp_while_loop_deletes_a_list.md`](https://github.com/clicklang/click/blob/master/mdtests/cpp_while_loop_deletes_a_list.md),
[`mdtests/cpp_while_loop_that_leaks_a_node_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/cpp_while_loop_that_leaks_a_node_is_refused.md)).

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
the equality's proof lineage, read only the queried operands' fact indexes,
and strip chains of zero additions through borrowed operands. Deterministic
regressions check unrelated fact populations and increasing expression depth;
the C `int64_returned_zero_identity` fixture covers the common kernel path.

Named standard-layout structs and classes may include private or protected
fields; Clang checks source access control, while sidecar views and ownership
provide memory authority. Reachable record and field declarations may originate
in explicitly locked project headers. Their spans retain that header's identity;
each function body and its field-use spans belong to that function's definition source.

Embedded mutable records with trivial destruction retain nominal child
identities and exact ABI sizes, offsets and alignment. Contracts can describe
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
size. Ordinary, expanded and retained checks cover an automatic descriptor
with a pointer field and a nested uint64 extent while preserving backing memory.
A nested self-pointer regression also constructs a child at a nonzero parent
offset and reads through the pointer to that child's own field.

Constructor bodies may come from declared, locked header dependencies. Scalar
member initializers can call nonthrowing observers through their checked
read-only contracts; lowering captures the call result before storing the
field. Exception-enabled normal-only imports permit these local objects when
destruction is trivial. Throwing construction, header destructor bodies, and
nested calls in constructor arguments remain outside this slice.

An ordinary `void` function may use a bare `return;` to leave an
execution path early. The importer records it as a return edge and runs
the live locals' supported destructors before exiting.

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
derived fields and tail-padding reuse remain outside this profile; polymorphic
classes have their own, below.

A virtual method's contract is its interface. A call through it, on a
reference or through `this`, is checked against the contract of the method
the receiver's static type names, whichever override the dynamic type
selects. Declare a pure virtual method's contract in an imported
`.interface.click` file, for example `int Shape::area(int scale) const { ... }`.
Each override inherits the interface of the method it overrides, as a Rust
trait implementation does
([Rust reference](../rust.md#trait-method-interfaces)): the interface's
`ensures` join its own, labeled `Square::area.interface_ensures_0`, and its
proof establishes them; an override that writes no `requires` takes the
interface's, and written ones must follow from the interface's, each clause
read exactly or decided as a bare comparison. The inherited clauses are read
with the override's own names for its parameters
(`mdtests/cpp_virtual_override_renames_its_parameters.md`). An override whose `requires` do not follow, or that the
sidecar does not state, is refused naming both methods:

<!-- verified-example: mdtests/cpp_virtual_method_interface.md -->
```click
import "interfaces/cpp_virtual_method.interface.click";
int Square::area(int scale) const {
    ensures result == scale + 1;
}
```

Without object state the interface reads nothing through `this` and holds
none of its resources, so an override whose contract needs its fields does
not refine it. A
reachable virtual method brings every method of the translation unit that
overrides it into the artifact, each checked, and refuses one outside the
selected and dependency sources; a call through a virtual
method reaches its overrides, so a call back through the interface from an
override is refused as recursion. Overrides in other translation units are
not seen, and are trusted to keep the interface, as any unverified code is.
A qualified call, `shape.Shape::area(scale)`, does not dispatch, and is
refused for a pure virtual method. A polymorphic class has at most one
public, non-virtual, polymorphic base at offset zero, whose whole layout its
own fields follow; its leading vtable pointer is named by no field and read
by no contract. A defaulted, implicit or empty destructor, virtual or not
and of any access, over fields with trivial destruction and a base of the
same kind, `virtual ~Shape() = default;`, only resets the vtable pointer and
runs no code a proof sees (`mdtests/cpp_polymorphic_virtual_destructor.md`).
A class may write its own destructor with a body, virtual or not, verified
against its contract as any destructor is, when its fields have trivial
destruction. A local's destructor is called directly, so its contract is the
class's own (`mdtests/cpp_polymorphic_destructor_runs_its_body.md`,
`mdtests/cpp_polymorphic_destructor_rejects_overclaim.md`). A base whose own
written destructor runs code is destroyed by the class's written destructor,
which may then have an empty body: after the body the importer calls the
base's destructor on the base subobject, as C++ destroys an object, and the
class's destructor contract owns the base's fields as `this->base.log` and
ensures what the base destructor ensures. A class over such a base that
writes no destructor of its own is refused
(`mdtests/cpp_polymorphic_base_destructor_runs_after.md`,
`mdtests/cpp_polymorphic_base_destructor_runs_after_rejects_overclaim.md`). It is reached by
reference or built in a local by its explicit constructor, `Square sq(3);`,
or by its implicit default constructor, `Stack<int> stack;`, when every field
has a constant default member initializer and its base, if any, has no
fields, base or constructor of its own: its fields are initialized from the
initializers, as for any record.
The compiler's setting of the vtable pointer is trusted; the constructor's
contract owns and establishes the object's fields. While the object
constructs its dynamic type changes, so such a constructor initializes its
members without reading `this` and has an empty body. Its base, if any, has
no base of its own, and is built first: by its own non-default constructor,
named first in the initializer list, `Square(int s) : Shape(7), side(s)`,
which the importer calls on the base subobject before the members, or, for a
base with no fields and no constructor, implicitly. The derived
constructor's contract owns the base's fields as `this->base.tag` and lends
them to the base's constructor
(`mdtests/cpp_polymorphic_base_construction.md`,
`mdtests/cpp_polymorphic_base_construction_rejects_overclaim.md`). Copies, objects returned by
value, covariant results and a pure
virtual method with a definition remain unsupported
(`mdtests/cpp_virtual_override_rejects_narrower_requires.md`,
`mdtests/cpp_virtual_override_keeps_the_inherited_guarantee.md`,
`mdtests/cpp_polymorphic_local_construction.md`,
`mdtests/cpp_polymorphic_local_construction_rejects_overclaim.md`,
`tests/cpp_import.rs::virtual_dispatch_refuses_construction_recursion_and_other_class_shapes`).

A polymorphic class's object may carry state, as a Rust trait's does
([Rust reference](../rust.md#trait-object-state)). A `class` block declares
model functions of the object. An interface file can provide that block
with the base method contracts. Each direct subclass defines the functions
on its own memory in the sidecar:

<!-- verified-example: mdtests/cpp_class_object_state.md -->
```click
import "interfaces/cpp_class_object_state.interface.click";
class Square : Shape {
    function size(this) -> int32 { this->side }
}
int Square::area(int scale) const {
}
```

The object is the sealed abstract resource `Shape__object`, with a field for
each function. A method of `Shape`, and a function's `Shape&` parameter,
hold it with no clause written and read `size(this)` or `size(shape)` as its
field. A `const` method or `const Shape&` keeps it, so an `ensures` reads it
as it was at entry; a mutable one may change it, which its `ensures` reads as
new and `old(size(this))` as at entry
(`mdtests/cpp_class_object_state_mutable.md`). A method of `Square` is stated on `Square`'s memory, `owns *this`, with
`size(this)` read as the definition; a `const` one only views it, `views
*this`, so a caller of it keeps every field of the object, not only the
definitions (`mdtests/cpp_class_const_method_keeps_fields.md`,
`mdtests/cpp_class_const_method_keeps_fields_rejects_overclaim.md`). An override of a `Shape` method
inherits that method's clauses read the same way, labeled
`Square::area.interface_ensures_0`. Its refinement is checked against the
`contract` named for it with `_iface` that states them on that memory. Where a
call converts a `Square` reference to a `Shape` one, as an argument or a
receiver, the importer places `Square__click_pack__Shape` before the call
and `Square__click_unpack__Shape` after it. The pack consumes the memory
and produces the object, with the definitions as its fields; the unpack
returns the memory with the definitions equal to the fields. A caller
passing a `Square` therefore knows the object's `size` is its `side`, and
after lending it as a `Shape&` that its `side` is the object's new `size`
and nothing of the `side` it lent
(`mdtests/cpp_class_object_state_mutable_reference_returns_new_state.md`).
Where the conversion is to `const Shape&`, the importer places
`Square__click_pack_const__Shape` and `Square__click_unpack_const__Shape`
instead: the pack views the memory and produces, beside the object, the
resource `Square__click_lent__Shape(object) { views *object; }`, which keeps
the memory lent until the unpack consumes both. Nothing can change the
memory meanwhile, so the caller keeps every field, and the same object
cannot also be handed over in that call as a mutable reference
(`mdtests/cpp_class_const_reference_keeps_fields.md`,
`mdtests/cpp_class_const_reference_lends_the_object.md`).

A polymorphic class template listed in `templates` carries object state
through a generic `class` block, as a Rust generic trait does
([Rust reference](../rust.md#trait-object-state)):

<!-- verified-example: mdtests/cpp_class_template_object_state.md -->
```click
import "interfaces/cpp_class_template_object_state.interface.click";
template<class T> class Wrap<T> : Holder<T> {
    function held(this) -> T { this->value }
}
template<class T> void Wrap<T>::put(T x) {
}
```

The object is the generic resource `Holder__object<T>`, and each instance
the import has, `Holder<int>`, holds it at its type arguments,
`Holder__object<int>`. A pure virtual method can be declared with
`template<class T>` in the interface file. Each instance uses the contract
at its types. `Wrap<T>`'s overrides are verified once, with `T`
abstract, against the interface read through its definitions, the
`contract` named for each with `_iface` stated once for every type too; an
override that does not keep it is refused there
(`mdtests/cpp_class_template_object_state_rejects_overclaim.md`). Each
instance of `Wrap` the import has, `Wrap<int>`, packs and unpacks with the
definitions at its types, its functions named by the instances' records,
`Wrap__int__click_pack__Holder__int`. A generic block names its template at
its own parameters, and its base at them or at concrete types. Classes
deriving from a generic defining class, and dispatches through one, remain
outside this slice.
A class template instance behind a record pointer field, `Node<int>` for
`Node<T>* head`, is completed for its layout though no use in the translation
unit completed it.

A defining class whose object's state is not in its fields, a stack whose
items are in nodes on the heap, names the resource holding it in its
`class` block and defines the functions from that resource's fields:

<!-- verified-example: mdtests/cpp_generic_class_state_in_a_resource.md -->
```click
template<class T> class Stack<T> : Container<T> {
    resource state: nodes<T>(this->head);
    function items(this) -> List<T> { state.items }
}
```

Each override of an object class method holds `owns state:
nodes<T>(this->head)` beside its memory, read where the clause is, so `push`
leaves `state` at the new head. The class's other methods state what they
hold, as a Rust type's own methods do beside its `impl` block's: an override
may call one that consumes and produces the resource itself,
`consumes before: nodes<T>(this->head); produces after:
nodes<T>(this->head);`, handing it `state` and taking back the instance it
produces (`mdtests/cpp_class_resource_state_override_calls_a_helper.md`).
The issue's stack implements `Container<T>` so, its `put` and `take` calling
its own `push` and `pop` (`mdtests/cpp_generic_stack_is_a_container.md`).
The pack consumes the resource with the memory, and the unpack produces a
new instance holding the object's final state, which a caller that lent its
own, `owns state: nodes<int>(stack.head)`, holds under `state` at its exit.
A `const` pack consumes it too, and the `const` unpack returns it with the
definitions equal to the object's kept fields, at the arguments it had at
entry, `cell(old(object->slot))`: the caller's view of the memory they read
is the lent resource's, which the unpack consumes, and an argument read at
entry is read with the authority held at entry
(`mdtests/cpp_class_resource_state_lent_as_const.md`,
`mdtests/cpp_class_resource_state_lent_as_const_rejects_overclaim.md`). The resource is named in a
class block whose base is its object's class; a class deriving from a
defining class does not hold one. A definition that ignores the resource is
refused at the override
(`mdtests/cpp_generic_class_state_ignored_is_refused.md`). A method's proof
folds a new instance of the resource under its name only once the old one is
consumed: `push` unfolds `state`, folds the old list back as the new node's
tail, then folds `state`.

An object function may also be a field's machine value, `function size(this)
-> uint64 { this->count }`, and the interface may compare it as an `Integer`
with the resource's state, `requires to_integer(size(this)) ==
length(items(this));`, as a Rust trait's clauses do: each override's
interface check decides that clause by exact match, and its proof restores
it, `push` applying `integer::uint64_add_to_integer` to the incremented count.

A generic body may pass a value of its abstract type argument to a method of
the same template at the same argument, `assign(x)` from `Wrap<T>::put`, as
it was read, and a class template's written destructor is its record's own,
exported and verified once for every `T`, even where no local runs it
(`mdtests/cpp_class_template_override_calls_its_own_method.md`). A
function's proof names a parameter's object state as its clauses do,
`apply(rest_cons(x, old(items(container))))`
(`mdtests/cpp_class_object_state_named_in_a_proof.md`).

The stack's destructor deletes its remaining nodes, its contract naming what
it destroys, `template<class T> Stack<T>::~Stack() { owns *this; consumes
list: nodes<T>(this->head); }`. A local `Stack<int> stack;` built from its
default member initializers is passed as a `Container<int>&` after its
caller folds `state: nodes<int>(stack.head)`, which the pack consumes and the
unpack gives back; the destructor consumes it at the local's scope exit
(`local_round_trip` in `mdtests/cpp_generic_class_state_in_a_resource.md`).

A class may derive from a defining class, and override its methods, when
its own `class` block names that class as its base. It defines the object's
functions on its own memory, or inherits each it does not write, read
through its base part:

<!-- verified-example: mdtests/cpp_class_subclass_override_keeps_the_interface.md -->
```click
class BigSquare : Square {
    function size(this) -> int32 { this->base.side + this->extra }
}
int BigSquare::area(int scale) const {
}
```

Each of its overrides keeps the object class's interface read with its own
definitions, labeled `BigSquare::area.interface_ensures_0`, and refines only
the `contract` named for it with `_iface`, not the method it overrides
(`mdtests/cpp_class_subclass_override_rejects_overclaim.md`). A reference to
a class another `class` block derives from, `const Square& square`, may
refer to an object of the derived class, so it holds the object class's
object as a `Shape&` does, and reads `size(square)` as its field; a contract
on it cannot read `square.side`. Where such a reference becomes a reference
to a base, nothing is packed. A call through it, or through `this`, to a
method that overrides one of the object class's names the dispatch
`Square__click_dispatch__area`, whose contract is that interface on the
object, whichever override runs; without a sidecar `class` block deriving
from the class, the dispatch's contract is the method's own
(`mdtests/cpp_virtual_call_through_a_derived_class_reference.md`). A qualified
call, `square.Square::area(scale)`, and a call on a complete object, a
local or by-value parameter, run the method named, against its own
contract. A conversion packs with the definitions of the class of the
complete object or reference it starts from: a `BigSquare&` passed as a
`const Square&` is packed by `BigSquare__click_pack_const__Square`, and a
local `Square` passed as one by `Square__click_pack_const__Square`
(`mdtests/cpp_class_subclass_local_object_packs_itself.md`).

Limits:
- An override in a class without a defining `class` block is refused.
- A class deriving from a defining class may inherit a method the sidecar
  states on an ancestor's memory only where each function the object
  class's interface for it reads is defined alike, read through the base
  parts; otherwise it overrides the method. The inherited method runs on
  the ancestor's part of the object, as its proof read it, and is not
  verified again
  (`mdtests/cpp_class_subclass_inherits_a_method_it_keeps.md`,
  `mdtests/cpp_class_subclass_inherited_method_rejects_redefined_state.md`).
- A method of a class another derives from holds its memory, not the
  object, so its call through `this` to a method that may dispatch to an
  override is refused, naming what each holds; a qualified call runs the
  method named. A reference to such a class holds the object, so a call
  through it of a method stated on the class's memory, one that overrides
  none of the object class's, is refused the same way
  (`mdtests/cpp_class_subclass_override_call_through_this_is_refused.md`,
  `mdtests/cpp_class_subclass_memory_method_through_a_reference_is_refused.md`).
  Supporting these calls requires a checked conversion between the object
  resource and the class memory or dispatch resource the callee needs,
  with evidence that the conversion is valid for the receiver's dynamic type.
- A class whose own fields reuse its base's tail padding is refused by the
  layout profile.
- A call through the interface inside a larger expression is an expression
  observer, whose contract must be read-only, so the object's call is
  written as its own statement
  (`mdtests/cpp_class_object_state_override_keeps_the_interface.md`,
  `tests/cpp_import.rs::class_object_state_refuses_undefined_overrides_and_inherited_methods`).

For discarded-result copy assignment between live lvalues, a resolved
`operator=` from a system header or declared in another translation unit is
checked as a call. An `extern` contract can describe the destination's
updated logical state, the source's state, and the returned reference.

A C++ function taking a record by value can declare contract value parameters
with `let`. For example, `let count: uint64;` and
`requires value.count == count;` give the contract a name for the entry
count independently of later writes to the parameter. A caller can relate
its record's entry count to a resource field in a precondition and pass
the count with `step(shorten, { count: old(source.count) });`. The call
checks the equality on the copied record. The copy's storage is local
to the callee, and copying pointer fields grants no backing authority.

Discarded-result trivial copy assignment between live lvalues of the same
nominal record lowers to shared C aggregate field copies. Clang must resolve a
non-deleted, non-virtual trivial copy assignment; the record and embedded
records require trivial destruction and no base subobjects. Const sources and
nested record projections are supported. The destination requires write
authority and the source requires read authority for every scalar leaf. Checked
Clang layouts preserve native pointer and unsigned extent values; copying a
descriptor transfers no backing-storage authority. Self-assignment preserves
the fields. User-defined assignment bodies and move assignment remain refused.

Copy-initializing a local from a live lvalue, as in `auto copy = source;`,
can use a resolved trivial copy constructor declared in a system header.
The constructor call takes the destination's address and a reference to the
source. Its `extern` contract can establish the destination's logical state
independently of the object's fields. The pinned libc++ test
`libcxx_span_copy_initialization_uses_an_opaque_contract` checks this with a
logical pointer and count.

Other copy construction and moves, default or partial aggregate initialization, multiple
non-destructible aggregate locals, broader nested lifetime combinations,
general inheritance, bit-fields, nested record construction,
and same-named record layouts remain explicit errors.
Nested scalar locals outside a `while` body, references to scalar locals, shadowing,
broader address-taking, pointer locals, pointer arithmetic outside the supported
indexed native object-pointer slice, nonliteral null-pointer conversions, multiple
indirection, call results outside the supported initializer, return-call and direct Boolean
condition slices,
indirect calls, loops other than `while`,
external specifications other than the [standard-library
contracts](#c-standard-library), and broader C++ syntax also remain outside
this end-to-end subset.

## Validation and supported profile

Capturing C runs preprocessing with controlled arguments and environment,
records the selected toolchain, dependencies, source and artifact, and refuses
inputs that change during preparation. Loading a capture checks the manifest's
internal identities and the available project inputs against the recorded state. Changed C sources, opened project-local
headers, configuration, or artifact bytes cannot reuse that lock. External
toolchain and header changes require a new explicit refresh to produce a proof
about that new environment. A supplied digest alone does not authenticate who
prepared a native-platform artifact.

Compiler-backed C imports accept the target `x86_64-unknown-linux-gnu` in two
modes. A C unit is prepared for the project's `target` and
`mode`, which a sidecar's `target` and `mode` directives must
match; without them the project uses the default mode, `userspace`. A
capture records both, so changing either triggers a refresh.
Prepared imports retain their target through verification and expansion.

| Mode | Fixed compiler profile |
| --- | --- |
| `kernel` | GCC, `-x c`, `-std=gnu11`, `-m64`, `-funsigned-char`, `-nostdinc`, and the optimization level. |
| `userspace` | GCC, `-x c`, `-std=c11`, `-m64`, `-fsigned-char`, `-nostdinc`, `-pthread`, `-D_POSIX_C_SOURCE=200809L`, and the optimization level. |

Every source is also prepared at the project's optimization level, which the
lock records with the target and mode.

### Optimization level

A project names one optimization level, `-O2` by default, and every C unit
is preprocessed with it, and every C++ unit exported at it, so `__OPTIMIZE__`
and the headers that test it read as the optimized build sees them. A unit's arguments may repeat the level but
not name another. At `-O2`, GCC assumes the program never overflows signed
arithmetic, never dereferences null, never accesses an object through an
incompatible type, and keeps the promises of the attributes it trusts. Click
proves the first two, checks the third
([undefined behavior](../language/c.md#undefined-behavior)), and refuses the
attributes ([Optimizer promises](#optimizer-promises)); C++ follows the same
policy ([C++ unit arguments](#c-unit-arguments)), so a verified claim
holds for the `-O2` build without `-fno-strict-overflow` or
`-fno-delete-null-pointer-checks`. An optimizing level still adds
`-fno-strict-aliasing`, because the check does not see the effective types a
callee or `memcpy` gives heap cells (`design/effective-types.md`). `"optimization": "-O0"` prepares the units
unoptimized and accepts the promise attributes, which GCC does not act on at
`-O0`.

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

During `click capture`, Click writes its system headers for the selected
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

A unit that names a C library's include directories with `-isystem` puts them
before Click's, so every header they supply is read from them, a locked input
like any other, and the proof then assumes that library's declarations. None of
the repository's fixtures does; `design/adler32/project/zlib/` uses Click's headers.

Configured forced includes and ordered `-D` and `-U` options select additional
preprocessing inputs. Other compiler options are rejected unless a named option
profile, described below, lists their exact text. Response files, plugins,
and execution hooks are always rejected. The compiler runs with a cleared environment;
only the configuration's supported variables are supplied. Use explicit
`SOURCE_DATE_EPOCH` when source depends on date/time macros.

Compiler invocation has output and time bounds, and failure or cancellation
stops its owned process group. Partial compiler output cannot become a
validated artifact. Dependencies come from the compiler's complete dependency
output, including configured system headers; source-map filenames are not a
substitute for that inventory.

The initial implementation states the working directory, source directories,
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

A C unit may set `"option_profile"` to a named option profile. The
profile admits further options beside the preprocessing options above, and
only for its target. The lock records the profile name beside each source's
complete argument vector, and loading refuses a lock whose profile differs
from the unit's.

The one profile, `linux-6.8-x86_64-kbuild`, is the option set of the recorded
Linux v6.8.12 `x86_64_defconfig` Kbuild compilation of `lib/rbtree.c` with
GCC 13, for the `kernel` mode. It exists for that in-repository
import. An option is accepted only where ignoring it cannot make Click accept
a program the compiler treats differently: the option affects only
preprocessing, whose result is the locked artifact, or only diagnostics, or
only code generation, or it makes the compiler's semantics stricter than
Click's or no weaker. The list is closed and keyed to exact option text. A
different value, an unlisted sibling, or an unknown option is refused with its
source and argument position, for example
``source `lib/rbtree.c`: unsupported compiler argument 50 `-O3`; ...``. Some
options are accepted only beside others that make them safe; without them the
option is refused with the missing one named.

Besides `-E` and the source operand, which the importer supplies itself, the
recorded vector has 102 options: 15 base preprocessing options, 4 that the
target fixes, 2 that the project's `-O2` level fixes, and 81 others with 77
distinct forms. All 77 are accepted, `-mno-sse` and `-mno-sse2` only
beside `-mno-80387`. The optimizer promises below are refused in the imported
source.

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
| `-fno-strict-aliasing` | Fixed | Added at an optimizing level: the strict-aliasing check does not see the effective types a callee or `memcpy` gives heap cells (`design/effective-types.md`). |
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
| `-O2` | Fixed | The project's optimization level, `-O2` by default. Optimization preserves the meaning of a program without undefined behavior, which is what Click proves; GCC's remaining unchecked assumptions are refused in the source (see "Optimizer promises"), and `__builtin_constant_p` is an unknown 0 or 1. |

### Optimizer promises

When the project verifies at an optimizing level, as it does by default, the
frontend refuses, with the attribute's location and the reason, every
attribute and qualifier that GCC's optimizer trusts as a promise from the
programmer, because Click does not check those promises. At `-O0`, GCC 13
does not act on them and they are accepted and ignored.

| Construct | At `-O2` | Reason |
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

A C++ unit refuses, at an optimizing level, `nonnull` (on the function or a
parameter), `returns_nonnull`, `const`, `pure`, `leaf`, `noreturn` (also as
`[[noreturn]]`), `returns_twice`, `malloc`, `alloc_size`, `alloc_align` and
`assume_aligned` on every declaration of a function it exports from the
project; `restrict`, and statement attributes other than `likely` and
`unlikely`, are refused in every mode. A function declared in a system
header is an axiom whose contract Click supplies, so its attributes are not
refused (`tests/cpp_import.rs`,
`cpp_optimizer_promises_are_refused_at_an_optimizing_level`).

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

## Calls into another translation unit

A selected or reachable function may call a project function that its
translation unit declares but does not define, such as one declared in a
header and defined in another `.cpp` of the project. The exporter records
that callee as `"external": true` with its kind, receiver, parameters, return
type and declaration span, and no body; its declaration's file is a
dependency like any other. The callee must be a `noexcept` free function,
static method or ordinary non-virtual method with external linkage that names
its parameters; a constructor, destructor or virtual method defined elsewhere
is refused, and so is a compiler builtin.

A sidecar that verifies the defining source too links the sources:
`verifying "client.cpp"; verifying "counter.cpp";` in
`examples/multifile-cpp`. Each
source is exported and lowered on its own, then the functions are joined by
name. A definition binds every other source's declaration of the function
whose interface matches it (parameter names may differ), so a call is checked
against the contract the sidecar proves of that body. The one-definition rule
is checked: two sources whose definitions of a function differ, whose
declarations of it differ, or whose layouts of a record differ are refused,
naming both sources. An inline function a shared header defines is the same
definition in every source that uses it.

A callee no linked source defines is checked against a contract the sidecar
states as an `extern` declaration, an assumption like any other external
contract; without one the call is refused, naming the callee
(`a_call_into_another_translation_unit_is_checked_against_a_contract` and
`linked_cpp_sources_refuse_an_unproved_callee_and_differing_definitions` in
`tests/cpp_import.rs`).

## C++ standard library

### The standard-library contract boundary

Clang parses the standard headers and resolves each call to a declaration.
Click selects a library contract using the resolved specialization and
overload, then checks the caller against that contract. Click assumes the
library contract and reports it as a standard-library assumption. The same
contract applies across standard-library implementations.

Each C++ standard-library interface follows
[library interfaces](../../concepts/library-interfaces.md): it describes
observable state and effects, such as a span's borrowed range, never the
library's private fields or method bodies.

### Current catalog and layout-backed accessors

The existing `std::span` and `std::array` interfaces still use layout-backed
state accessors, as described below. This is an implementation dependency, listed
among the [departures](../../concepts/library-interfaces.md#where-the-implementation-departs-from-this);
the contract boundary above is the target for replacing it.
When a caller uses these layouts from system headers, keep those headers
inside the C++ unit root and list them as dependencies. A project with a
separate sysroot can place it under that root and use its build's `--sysroot`
and `-isystem` arguments.

The pinned libc++ tests `libcxx_span_empty_checks_abstract_state` and
`libcxx_span_assignment_carries_abstract_state` exercise this boundary with
explicit `extern` contracts. The observers use state in a Click abstract
resource, and the assignment contract updates the destination's resource
with the source's pointer and count. A caller without the required state is
refused. The built-in span contracts still use the layout to establish
descriptor state for constructed and returned spans.

A function declared in a system header (one reached through `-isystem`, a
system include path, or `#pragma clang system_header`) is an axiom. The
exporter records its kind, receiver, parameters and return type, keyed by its
qualified name and canonical signature, and never exports its body. Click
prepares it as an opaque function, and each call is checked against a
contract:

- Click supplies contracts for the standard functions in its catalog, keyed on
  the standard name and signature. The sidecar is parsed with them appended; the
  catalog itself is never written into a sidecar by expansion.
- The catalog's contracts are Click text, written as a sidecar writes a
  class template's methods ([class templates verified once](#class-templates-verified-once)):
  `library/cpp/span.interface.click` states the dynamic-extent `std::span<T>` methods
  as `template<class T> unsigned long std::span<T>::size() const { ... }`
  and the static-extent ones as `template<class T, std::size_t N>
  unsigned long std::span<T, N>::size() const { ensures result == N; }`.
  The dynamic pointer/count constructor is also a library interface,
  `template<class T> std::span<T>::span<T *>(T* first, unsigned long count)`.
  Its Click contract has no exceptional outcome, including on standard
  libraries that omit `noexcept` on this overload. It consumes unwritten
  descriptor storage, produces it initialized and
  establishes the data pointer and count, without granting backing authority.
  Static-extent constructors and iterator-pair overloads are outside that model.
  `library/cpp/array.interface.click` states `std::array<T, N>`, whose element
  accessors are each a mutable and a `const` overload written as two
  template methods, `T& std::array<T, N>::front()` and `const T&
  std::array<T, N>::front() const`.
  The importer keeps only a name table
  (`src/languages/cpp/standard_library.rs`): which qualified names and
  signatures are instances of which library method, at which element types
  and extents. The table maps `std::span<int, 4>::size` to
  `std::span<T, N>::size` and `std::span<int>::size` to `std::span<T>::size`;
  it maps no static extent that is `std::dynamic_extent` or whose byte size
  overflows a `uint64`, and no `std::array` of `const` elements, so such a
  call is refused.
  Each called instance is written out from its template, and a library
  template no call instantiates is dropped. A sidecar does not restate a
  library interface: an `extern` for `std::span<int>::size` is refused, naming
  the library. `library/cpp/as_writable_bytes.interface.click` states the function
  template `std::as_writable_bytes<T, N>`, named in its own segment by its
  element and extent as Clang names the instance,
  `std::as_writable_bytes<int, 18446744073709551615>`; the table maps it
  at `std::span<int>` only. A user's function template outside a class is
  written out the same way, at the arguments its instance's segment names.
- A call to a standard function with no catalog contract is refused, naming
  the function. A sidecar may state its own `extern` contract instead, which is
  an assumption like any other external contract. Its head matches the C++
  declaration's parameter types in order and provides names for the contract.
  For example, `extern int* ministd::identity(int* p)` names its parameter
  `p`, and `extern int ministd::Box::get() const` has an implicit `this`
  (`tests/cpp_import.rs`, `axiomatic_*`).
- This slice admits a standard function when its declaration is `noexcept`
  or a matching Click catalog contract establishes that it cannot throw.
  One returning a record by value constructs it in the caller's destination.

A sidecar writes a standard type as C++ does,
`int32 probe(std::span<int>& s)`, `uint64 probe(std::span<const unsigned char, 32>& s)`
or `std::array<int, 4>& a`.
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

A contract that views a span's backing range reads the descriptor to name
that range. For a borrowed dynamic span, grant `views std_span_data(s);`
and `views std_span_size(s);` before the backing-range clause.

A refused catalog precondition reached after execution also names reads by
these accessors. Historical reads keep their `at(...)` qualification, for
example `at(<state A>, std_span_size(s))`, rather than a carrier-cell index.

The `std::span<T>` entries are generic over the element type `T`, which may
be `int`, `unsigned int`, `unsigned char` or `std::byte`, each possibly
`const`; a `std::span<const T>` holds a `const T*`, and its element accessors
return `const` references. They cover a
dynamic-extent span's `size`, `size_bytes`, `data`, `front`, `back`,
`operator[]`, `first`, `last` and `subspan(offset, count)`:

A dynamic-extent `subspan` retains the catalog's implication-shaped count
precondition. Before recovering its returned view, the implicit closer proves
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
element references. A caller can bind one and use it for reads or, for a
mutable reference, writes. A caller can also read it as a direct scalar
initializer or return value. A read of the returned reference inside a larger
expression, such as `return s[0] == 67;`, is currently unsupported.
A defaulted argument is imported as the constant Clang evaluates for it, so
`subspan(1)` passes `std::dynamic_extent` as its count and verifies as the
subview to the end.

A static-extent `std::span<T, N>` keeps its extent in its type. libstdc++'s
extent member is `[[no_unique_address]]` and empty, so the importer leaves it
out and the record holds only the data pointer; any such stateless member of
an empty, trivially copyable class is left out the same way. Its library
methods state the size as the extent, which an instance writes as a literal,
`4u64`: `size()` is `N`, `size_bytes()` is
`N * sizeof(T)`, and `front`, `back` and `operator[]` require an index below
`N`. `first`, `last` and `subspan` take a runtime count and return
dynamic-extent spans.

`std::array<T, N>` holds its elements in an inline array field, which the
record profile admits for native element types. Its `size()` is `N`; `data()`
is `&std_array_data(a)[0]`; and `front`, `back` and `operator[]`, in their
const and mutable overloads, require an index below `N` and return
`&std_array_data(a)[i]`. A read can name just the selected element with
`views std_array_data(a)[1];`, and a write requires
`owns std_array_data(a)[1];`. Owning a neighboring element or viewing the
written element does not authorize the write. Resource clauses also accept
the imported field name, such as `views a._M_elems[1];`, on a record
reference. Expansion retains the field and its subscripts, and a failed
resource-clause evaluation names that place.

The library also states dynamic-extent
`std::as_writable_bytes(std::span<int>)` and
`std::as_writable_bytes(std::span<unsigned int>)`. Both return a byte view of the
same storage: its data is `std_span_data(input) as (uint8 *)` and its native uint64
length is `std_span_size(input) * 4u64` on the pinned ABI. The conversion copies no backing bytes, requires no
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

A C source entry may set `"projection": "dependency-closure"` and list the
functions to select by their C names:

```json
"sources": {
  "arraylist.c": {
    "projection": "dependency-closure",
    "functions": ["array_list_get_idx"]
  }
}
```

The names must identify definitions in the translation unit's primary
source file (the file the first line marker names). With `functions` omitted
or empty, projection starts from every function defined in this file.
The named roots are recorded in the lock. Run `click capture` after
changing them.

Projection keeps the roots and, transitively, file-scope declarations
that define names a kept declaration mentions. That includes types, tags,
enumeration constants, typedefs, objects, prototypes, and helper bodies.
An unsupported construct in a kept item is rejected at its original
location. An unreferenced sibling can use features outside Click's C
subset. Only functions with proof blocks in the sidecar are verified.

Two rules keep the omission checked rather than permissive:

- An exact `extern typeof(f) f;` redeclaration is never needed to type a use
  of `f`, because it repeats `f`'s own type with nothing added. The Linux
  `EXPORT_SYMBOL` macro emits one per exported function, beside its export
  storage and `.export_symbol` assembly, which nothing names. Export storage
  and export assembly are therefore outside the claim.
- If an omitted declaration carries the `constructor` or `destructor`
  attribute, the projection is refused, because such a function runs
  without being named.

With explicit function roots, Click refuses file-scope assembly and GNU
asm labels. Both can bind symbols through strings that the name-based
dependency calculation cannot follow.

Every other declaration that defines a needed name is kept, including
redeclarations that add attributes such as `weak`. Omitted declarations are
blanked in place, so line numbers and original-source locations are
unchanged. The option is part of the import configuration and therefore of
the lock's identity.

The dependency calculation is conservative. Its name-based analysis can
keep additional declarations with the same spelling. The prepared artifact
and lock still cover the entire preprocessed translation unit and its inputs.

### C89 compilation with native headers

On x86-64 Linux in userspace, an explicit `-std=c89` uses GCC's C89
preprocessor mode and its native feature-test macros. Supply the build's
include directories with `-isystem`; Click inventories the opened headers.
The retained source still uses Click's supported C subset. The C89 profile
also accepts `-fPIC` and `-fstack-protector-strong`.

For explicit function roots in that mode, Click reads balanced GCC
`visibility push(default)` and `visibility pop` directives and GCC
diagnostic push, pop, and ignored-warning directives. A declaration with an
assembler label can leave the projection only if its plain symbol name is
outside the retained dependencies. File-scope assembly is still refused.

At `-O0`, this rooted import also accepts `-fvisibility=hidden`. Retained
external declarations then need explicit default visibility. This preserves
the source-level linkage of the projected definitions. See the unchanged
[cJSON integration](https://github.com/clicklang/click/blob/master/integrations/cjson/README.md).

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
with the optional `library_assertions` field of a unit source. For example (replace the
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
The unit description, artifact, compiler command, and input closure are part of the import identity. A changed pin requires an
explicit edit of the project file and a lock refresh.

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
