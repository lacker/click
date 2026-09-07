# Add modules and imports for Click specifications

Click currently has one user sidecar per verification entry point and one
compiler-embedded `stdlib/prelude.click`. Reusable logical declarations must
therefore be copied into each sidecar or added to the global prelude. That is
adequate for the first standard-library types, but it does not scale to
project-local models, shared contracts, or a standard library divided into
coherent source files.

The eventual import facility should be an ordinary part of Surface Click, not
a second Rust-only concatenation path for the standard library. The concrete
surface syntax, whether imported names are qualified by default, and whether
explicit export lists are needed remain design decisions. A schematic use is:

```click
import "models/list.click";
import "models/tree.click";
```

Imports are local specification dependencies. They do not execute code,
perform network access, or silently add C translation units to the set being
verified.

## Violated invariant

A reusable Click definition should have one source of truth and the same
checked meaning wherever it is imported. Loading must be deterministic,
diagnostics must retain the defining file and source location, and adding an
unrelated module must not change name resolution or cause project-wide work
for a targeted verification.

## Intended regression

Create a small three-file specification project:

- `list.click` declares a generic algebraic `List<T>`, a recursive function,
  and a generic theorem;
- `tree.click` imports `list.click` and declares a tree model whose summary is
  a list; and
- the entry sidecar imports `tree.click` and applies both transitive
  definitions while verifying a small unchanged C function.

The entry point must not repeat either imported declaration. Importing the
same file through two dependency paths must install each declaration once.
Changing `list.click` must invalidate its dependents but not unrelated
verification targets.

Negative regressions reject a missing file, an import cycle, conflicting
public names, and an imported file that attempts to add a verification target.
Errors identify both the importing site and the relevant defining file.

## Acceptance criteria

- Surface Click has documented local-file import syntax with paths resolved
  relative to the importing file under a declared project root. Imports are
  canonicalized, deterministic, and perform no network access.
- Imports are transitive. A file reached more than once is loaded once, and a
  cycle is rejected with the complete, bounded import chain.
- Algebraic types, pure functions, predicates, theorems, resources, named
  contracts, and supported external C specifications can be exported and
  imported without changing their checked semantics.
- The entry sidecar alone selects `verifying` C sources. Imported modules
  cannot silently broaden the verification boundary.
- Name visibility has one documented rule. Duplicate or ambiguous public
  names fail at their source locations; imports cannot shadow built-ins,
  standard-library declarations, or local definitions accidentally.
- Type checking, theorem verification, recursive-definition grouping, and
  declaration-order rules operate over the resolved dependency graph rather
  than raw textual concatenation.
- Diagnostics and retained proof artifacts preserve stable module-qualified
  definition identities and original file locations.
- The standard library can use the same module mechanism to split
  `stdlib/prelude.click` into coherent files; there is no separate unchecked
  stdlib include convention.
- Incremental and `--changed-since` selection include transitive specification
  dependencies. An unrelated imported module does not trigger verification or
  complete-environment cloning.
- Positive, negative, duplicate-import, transitive-invalidation, and
  multi-size dependency-scaling regressions pass with `scripts/check.sh`.

This is not an MVR dependency: the minimum rbtree result can use one sidecar
and the embedded prelude. It becomes important when its models and reusable
proof libraries are shared across verification targets.

