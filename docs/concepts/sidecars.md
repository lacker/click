# Files and sidecars

Click specs live beside C source files. The C file contains executable code.
The `.click` file names the C file and gives contracts for functions in it.

A tiny project might look like this:

```text
increment.c
increment.click
```

The C file contains the implementation:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```c
int32 increment(int32 x) {
    return x + 1;
}
```

The Click sidecar names the C file and specifies the function:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures increments: result == x + 1;
}
```

The function signature in the `.click` file must match the C function. The body
of the Click function is not executable C; it is the contract and proof surface
for the C function.

Use a `*.interface.click` file for contracts whose implementations are outside
the proof. A sidecar imports the interface by path. It must prove the
interface's preconditions at calls and can then use its guarantees. Click
reports that dependency among the caller's assumptions.

## The `verifying` clause

Each sidecar starts with one or more source declarations:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```click
verifying "increment.c";
```

This tells Click which C source files are part of the verification unit. Larger
sidecars can name multiple C files when a proof depends on helper functions.

A source alias can select a translation unit's function definition. This is
needed when several selected files include a `static inline` helper with the
same source name:

<!-- verified-example: mdtests/qualified_inline_function_contract.md -->
```click
verifying "first.c" as first;
verifying "second.c" as second;
int32 first::helper() {
    ensures result == 1;
}
```

`first::helper` selects `helper` from `first.c`; calls in that translation unit
use this contract. Call binder maps use the same qualified name, as in
`step(first::helper, { before: input })`; the selected definition must be
the actual call at the execution frontier. The alias is resolved in the declaring sidecar and keeps
that binding when the contract is imported. An unqualified head still works
when the source name identifies one definition. Ambiguous names, unknown
aliases, missing definitions, and multiple ordinary contracts for one C
definition are rejected. Named contracts remain the way to give one function
additional separately proved interfaces.

A directory can set the C target and modeled runtime once for its sidecars in
`click.project.json`, with optional `target` and `runtime` string fields. For
example, `{"target":"x86_64-unknown-linux-gnu","runtime":"modeled-pthread"}`
selects the conditional pthread model. A sidecar in a subdirectory without
its own file uses the nearest one above it. The file can also declare the
project's compiler-import units ([Project units](../reference/cli/capture.md#project-units)).
Existing `target` and `runtime`
directives in `.click` files remain valid when they agree with the project
config. The selected profile is bound to proof artifacts and incremental
sessions; configuration changes require a fresh verification.

## Local specification imports

A sidecar can reuse logical declarations from another local Click file:

<!-- verified-example: mdtests/specification_imports.md -->
```click
import "specification_imports_model.click";
```

Imports are relative to the importing file, transitive, and confined to the
sidecar's project. The project root is the nearest directory, from the
sidecar's own upward, that holds a `click.project.json`; a sidecar with no
project file above it is a project of its own, rooted at its directory. Paths
are canonicalized to stable project-relative module identities; cycles,
missing files, imports that leave the project, and ambiguous unqualified
declarations are errors. Sidecars that share a specification belong to one
project: the `examples/rbtree` project holds the shared model in
`rbtree-model/` beside the `rbtree-insert/`, `rbtree-erase/` and
`rbtree-augmented/` sidecars that import it as `../rbtree-model/...`. The
boundary is a Click concern, independent of version control, and every
command uses the same one.
Libraries may export algebraic types, predicates, pure functions, resources,
theorem statements, named contracts, C function specifications, and tactics.
An imported file's `verifying` declarations select sources when that file is
verified itself; they do not add translation units to the importer. The entry
file selects the C sources for its own verification, including implementations
whose imported contracts it uses.

An import provides declarations, not a request to run proofs. Verifying an
entry sidecar checks only theorem, C function, and tactic proofs owned by that
entry. It may assume imported theorem statements and the well-formed contracts
of imported functions and tactics. Imported C signatures must still match the
implementations supplied by the entry. Select a library file itself—or a
directory scope that contains it—to check the library's proofs. Circular theorem justification and
the existing checked-recursion rules are enforced independently of this
selection boundary.

## Click library imports

A Click library module has a `click::` path that mirrors its file under
`library/`.

<!-- verified-example: mdtests/click_library_import.md -->
```click
import click::c::string;
```

`click::c::string` names `library/c/string.interface.click`. Importing a module twice is accepted. An unknown
module, or a path outside the `click` root such as `std::list`, is refused at
the import. A project file is always imported by a quoted path. A module's
library imports reach the files that import it, like its other declarations.

Without an import a file sees the implicit modules: `click::nat`,
`click::list`, `click::option` and `click::result`, and the
[verifier primitives](../reference/language/index.md#verifier-primitives),
declared in `click::primitives` and `click::c::builtins`. Library contracts come
with the code instead of an import: when the verified C declares or calls
`memcpy`, `memcmp`, `memset` or `strlen`, through `<string.h>` or its own
prototype, the file sees the C string contracts and proof declarations in
`click::c::string`, along with the shared `click::bytes` predicates used by
the contracts
(`mdtests/a_string_function_call_brings_the_c_string_contracts.md`).
A short path such as `string::readable` requires an import of its module. A
selective import can bring `readable` into scope by itself, and the full
`click::c::string::readable` path can be used directly
(`mdtests/string_predicates_need_an_import_without_a_string_function.md`).
The C++ and Rust library contracts are generated for the calls a program
makes, so they too arrive with the code.

<!-- verified-example: mdtests/a_cited_library_theorem_is_available_after_its_import.md -->
```click
import click::integer;
```

A proof that cites a theorem of a module the file does not import is refused
before any proof runs, and the message names the import to add
(`mdtests/a_cited_library_theorem_needs_its_module_import.md`).
A predicate, function, or resource of an unimported module is not visible
either, so a file may declare its own declaration with that name
(`mdtests/an_unimported_library_name_is_free_for_a_user_definition.md`,
`mdtests/an_unimported_library_resource_name_is_free_for_a_user_definition.md`).
A resource named in a contract without its module's import is refused with
the import to add (`mdtests/a_library_resource_needs_its_module_import.md`).
Built-in closers such as `close()`, its arithmetic, and loop-invariant closing
apply library theorems as part of their own reasoning, whatever the file
imports. They name a library theorem by its qualified identity, such as
`click::integer::int32_less_equal_transitive`, so a file may declare
a theorem with a library theorem's bare name: a bare citation then names the
file's theorem, a path names the library's, and the tactics keep the
library's (`mdtests/a_file_theorem_may_share_a_library_theorem_name.md`).
When `click expand` writes such a step out, it writes the theorem by the
shortest name that resolves to it in the file: its bare name after a
selective import, `integer::name` when the module is in scope, and otherwise
the full `click::integer::name` path, which needs no import. Diagnostics name a library theorem by its qualified
identity.

### Qualified library names

A library declaration also has a qualified name: its module path and its
name. A full `click::` path needs no import and brings its module, as an
import would; a module in scope, implicit or imported, is named by its last
segment:

<!-- verified-example: mdtests/qualified_library_names.md -->
```click
theorem append_nil_by_paths(xs: List<int32>) {
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(click::list::append_left_identity(xs));
    }
}
```

A short path to a module the file does not import is refused, and the
message names the import or the full path to write
(`mdtests/a_module_path_needs_its_module_in_scope.md`). A full path whose
last segment is not a declaration of its module is refused too
(`mdtests/a_full_path_must_name_a_module_declaration.md`).

A selective import brings bare names into scope:

<!-- verified-example: mdtests/a_selective_import_brings_bare_library_names.md -->
```click
import click::list::{append, length};

theorem append_nil_by_bare_names(xs: List<int32>) {
    ensures append(List<int32>::Nil, xs) == xs by {
        apply(list::append_left_identity(xs));
    }
}
```

Without a path or a selective import, a function, predicate or theorem of
`click::nat`, `click::list`, `click::bytes`, `click::c::string` or
`click::permutation` is not in scope by its bare name, even when the module is implicit
(`mdtests/a_bare_library_name_needs_a_path_or_selective_import.md`,
`mdtests/a_bare_list_theorem_citation_needs_a_path_or_selective_import.md`).
`import click::bytes;` puts the module in scope, so a sidecar writes
`bytes::equal`
(`mdtests/a_bytes_import_puts_the_module_not_its_names_in_scope.md`). A C
string call brings the `bytes` contracts but not the module name, so a
sidecar without the import writes the full path, `click::bytes::all_equal`
(`mdtests/a_string_function_call_brings_the_c_string_contracts.md`).
A file may therefore declare its own `append`
(`mdtests/a_file_may_declare_a_library_function_name.md`). A selectively
imported name that a file also declares, or that two selective imports
bring, is refused, as Rust refuses a clashing `use`
(`mdtests/a_selective_import_cannot_clash_with_a_file_declaration.md`).
Types and constructors such as `Nat`, `List` and `List::Cons` keep their
bare names, as does the primitive conversion `to_nat`. When `click expand`
writes out a theorem of these modules, it writes it by its bare name when a
selective import brings it, otherwise as `module::name`, such as
`list::append_cons`, when the module is in scope, and otherwise by its full
`click::` path.
Every library module with theorems, functions or predicates now uses
these qualified names; the native-width integer lemmas and wrapping
operations are `click::integer` declarations, such as
`integer::int32_positive_is_nonnegative`, and keep their width prefixes
(generic width-free names were not taken, maintainer, 2026-11-09).

## Contracts are per function

Each function block in a sidecar describes one C function:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```click
int32 increment(int32 x) {
    requires x < 2147483647;
    ensures increments: result == x + 1;
}
```

The `requires` clauses describe what callers must provide. The `ensures`
clauses describe what the function promises when those requirements hold.

## Where examples live

There are two kinds of example material in this repository:

- `mdtests/`: small, self-contained markdown tests. These are best for focused
  proof patterns and regression tests.
- `examples/`: larger example projects with ordinary `.c` files and `.click`
  sidecars. These are best for library-shaped verification examples. Most
  are one directory; `examples/rbtree` and `examples/pcg` are projects whose
  sidecars, in several directories, share one `click.project.json`.

For learning Click, follow the introductory concept pages and then read the
small mdtests listed in the examples catalog. For seeing how proofs are organized at a
larger scale, read the project fixtures under `examples/`.
