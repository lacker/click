# Add modules and imports for Click specifications

P1: an MVR dependency. The rbtree insert fixture copies the roughly 5000-line
`examples/rbtree-model` library because a sidecar cannot import it. The copy
buries the proof, is re-verified on each local run, and sits outside the
library's ordinary audit coverage. This issue provides a shared source of
truth and makes partial verification useful without recursively running all
imported proofs.

## Accepted design, 2026-09-13

These decisions were agreed with the user. They supersede the earlier
one-level-only import proposal and the proposal to recursively verify a
selected proof's dependencies. Implement the design below; the remaining
choices about internal APIs and project-root configuration are implementation
details, not a request to redesign the language or its verification policy.

### File modules and import syntax

One `.click` file is one module. There is no separate module declaration,
package manager, network resolution, or package registry. Imports are an
ordinary Surface Click declaration:

```click
import "../rbtree-model/rbtree_model.click";

verifying "rbtree.c";

// Local contracts and proofs use the imported model.
```

- Resolve a path relative to the importing file, within a declared project
  root. The root must support sibling example directories, including
  `examples/rbtree-insert` importing `examples/rbtree-model`; do not assume
  every entry file's containing directory is the entire project root.
- Use canonical file identities, deterministic loading, and original source
  locations. Load a module once per verification session even when several
  import paths reach it. Diagnose missing files, paths outside the root, and
  import cycles locally, with a bounded import chain.
- Support transitive imports in the first delivery. A module can import
  another module; no temporary one-level restriction is needed.
- Initially all supported declarations are public, and names from the import
  closure are available unqualified. Preserve existing declaration namespaces;
  reject conflicting names rather than shadowing them or selecting a winner
  by import order. Reaching the same declaration twice is not a conflict.
- Each module resolves its definitions against its own declarations, imports,
  and standard library. Importers cannot supply missing names or change an
  imported definition's meaning. Internally retain module-qualified declaration
  identities even though users initially write unqualified names.
- Qualified surface names, import aliases, selective imports, private
  declarations, and explicit export lists are deferred.

The first delivery imports algebraic types, pure functions, predicates,
theorems, and resources. Importing a file containing `verifying` is rejected:
only an entry sidecar chooses C translation units. Imports cannot silently
add executable verification targets. Broader shared named-contract and
external-C-specification support follows under the same boundary rules.

### Partial verification is conditional verification

**Selection determines which proof obligations run. Imports determine which
declarations are available.**

Loading an import resolves and checks declaration interfaces and the structural
rules required to give them a valid meaning. It does not execute the imported
proof scripts. A selected proof may use imported theorem statements and
called-function contracts as assumptions without recursively proving their
implementations. This applies consistently to logical theorems and C calls.

Successful partial verification establishes the selected local claims given
those interfaces. It does not establish that all imported claims, all callees,
or the whole codebase are valid. An unselected proof may fail when separately
selected without preventing an otherwise valid local proof from succeeding.
Malformed interfaces and forbidden dependency structures still fail loading;
partial verification is not permission to accept ill-defined declarations.

This does **not** change circular forbidden-ness. Preserve the existing rules
against circular theorem justification, self-justification, and invalid
recursive definitions/contracts. Module boundaries and selection must not
launder a forbidden cycle into apparently independent assumptions. Retain the
existing supported, checked recursion rules; do not reject valid recursion
merely because unrestricted circular justification is forbidden.

Do not implement recursive dependency-proof execution as a prerequisite for
partial success. Do not require persistent proof caches or previously verified
dependency artifacts to make local verification possible.

### CLI scope and reporting

Extend the existing command forms instead of adding a `verify-module` command.
These examples specify the intended import-aware behavior:

```sh
click verify models/tree.click
click verify proofs/insert.click
click verify models/tree.click:80:1
```

- A file target checks every proof defined in that file, assuming imported
  theorem statements and called-function contracts.
- A source-location target checks only the selected proof unit under the same
  interface assumptions. The current documented behavior that also verifies
  called C functions must be updated to this agreed partial-selection policy.
- A directory/project target checks every proof in its selected scope.
  Importing a module is not itself a request to execute that module's proofs.
  A whole-project verification scope must include the library modules as well
  as the entry sidecars, so their assumptions are discharged by checking their
  own proofs. Document a concrete full-scope invocation for the rbtree examples
  using the existing directory/project forms and discovery behavior.
- Report the selected scope, for example `1 selected proof verified`; do not
  label a successful partial run as verification of the entire dependency
  closure. Keep the scope and assumption boundary in retained verification
  results and proof artifacts as well as CLI output.
- A new named-claim selector for `verify` is not required. Source coordinates
  already select a proof unit; `audit` already has `--claim`.

Directory/project verification must avoid repeatedly running a library proof
just because several selected sidecars import it. The full normal gate must
select and verify the relevant library proofs, not silently omit them because
they have no C `verifying` declarations.

### Shared tooling, changes, and efficiency

Use one resolved module graph and stable source identities through ordinary
verification, profile, expand/reverify, audit, and fixture gates. A definition
or tactic in an imported file belongs to that file; diagnostics and expansion
must preserve that ownership rather than assigning it a concatenated sidecar
location. Audit must be able to select the library itself, and a local audit
must respect the same proof-selection boundary as local verification.

Transitive imported inputs participate in artifact identities and change
detection. A changed imported statement or definition cannot leave an old
dependent result marked current. Existing `--changed-since` must either use
correct import-aware invalidation or conservatively rebuild the selected
scope; it must never ignore imported changes or silently expand the selected
scope to run every dependency proof. Precise incremental selection can follow.

Loading and interface checking are distinct from executing proofs. Share
parsed modules and resolved environments within a session. Do not clone the
complete environment per function/tactic, reparse a diamond's common dependency,
or scan unrelated project files for a selected entry. Deterministic multi-size
regressions must measure the actual module/declaration/selection work, not just
warm wall-clock time. Persistent cross-run proof caching is deferred.

## Violated invariant

A reusable Click definition must have one source of truth and the same meaning
wherever it is imported. Selected proofs must be checked under their declared
interfaces without implicitly executing unrelated or imported proofs. Full
verification must check the complete selected project, with the existing
non-circular justification rules intact. Neither importing nor partial
selection creates unconditional theorem authority for an unproved assumption.

## First implementation delivery

1. Implement transitive local imports, canonical identities, deterministic
   resolution, module-owned names and source spans, collision/cycle diagnostics,
   and the initial declaration subset above. Select and document the smallest
   project-root configuration mechanism compatible with existing CLI inputs.
2. Separate declaration loading from proof selection/execution. Implement file,
   location, and project scope as specified, including conditional result
   reporting and preservation of circularity/recursion rules.
3. Carry the same module inputs, source identities, and selection through all
   proof tools. Make existing incremental handling safe; a conservative rebuild
   of the selected scope is acceptable initially.
4. Convert the copied insert fixture into `examples/rbtree-insert` importing
   `examples/rbtree-model/rbtree_model.click`, coordinated with
   [rbtree-example.md](rbtree-example.md), package I1. Preserve the unchanged C
   and the honest current proof frontier; this issue does not require finishing
   the insert proof or turning an unfinished proof into an accepted claim.
   Retain explicit negative/frontier fixture coverage if needed to keep the
   normal examples gate green. Remove the duplicated library source.
5. Land regressions and documentation with `scripts/check.sh` green. Do not
   recursively spawn Click commands or build a second concatenation/checking
   path for imports; use the shared bounded engine.

## Intended regressions and acceptance criteria

- A three-file project has `list.click` declaring a generic algebraic list,
  pure function, and theorem; `tree.click` imports it and defines a tree model;
  an entry imports `tree.click` and verifies unchanged C without copying either
  library. Include imported predicates and resources.
- A diamond loads each module once; changing import order does not change
  meanings. A module cannot capture an importer-only name. Conflicts with
  local, imported, or built-in names fail in their existing namespaces.
- Missing imports, escaped project roots, import cycles, conflicting names,
  and an imported `verifying` declaration receive bounded source diagnostics
  identifying the importing site and relevant defining file.
- A well-formed library theorem with a deliberately failing proof can be used
  by a passing selected local proof. Selecting the library proof, or running
  the full scope containing it, fails. Repeat the boundary test for a caller
  whose callee has a well-formed contract but a failing implementation proof.
- Deterministic execution counters show that file/location selection runs
  exactly its selected proofs, not imported theorem proofs, unselected callee proofs, or
  unrelated sibling proofs. Full project selection checks all selected modules
  once, including theorem-only libraries.
- Self-justification, mutually circular theorem justification, and forbidden
  recursive definitions remain rejected under partial and full selection;
  existing valid checked recursion remains supported. Import cycles are also
  rejected independently of proof selection.
- Imported declarations retain original locations and module identities in
  diagnostics and artifacts. Representative local and library targets agree
  across verify, profile, expand/reverify, and audit, without modifying an
  unrelated imported proof during local expansion.
- Imported-input changes invalidate affected retained results and incremental
  reuse. Unrelated changes do not trigger dependency-proof execution. If precise
  incremental selection is deferred, test the documented conservative fallback.
- Multi-size regressions cover chains, diamonds, shared libraries across
  selected entries, and selected versus unselected proof bodies. Source and
  interface preparation is proportional to the loaded input up to indexing
  factors; proof execution is confined to the selected obligations.
- The rbtree model has one source of truth, its own verification/audit target,
  and full-gate coverage. C remains unchanged. Focused tests, documentation
  checks, and the full unpiped `scripts/check.sh` pass.

## First implementation delivered, 2026-09-13

The first delivery is implemented on the module graph used by `verify`,
`profile`, `expand`/reverify, `audit`, and the example harness. The CLI chooses
the nearest Git worktree root (or the entry directory outside Git), resolves
and canonicalizes transitive local imports once, and uses stable
project-relative module identities. It preserves source ownership, rejects
cycles, escapes, missing modules, collisions, importer capture, imported C
selection/specifications, and circular theorem justification before proof
selection.

File verification selects proof units owned by the entry file; location
verification selects exactly one such unit. Imported and otherwise unselected
theorem statements and called-function contracts are scoped assumptions, not
recursively executed proof obligations. Retained C proof results record the
entry, selected units, and assumed theorem/function interfaces, and their
artifact identity covers every reachable Click source and import edge. Full
directory discovery selects each `.click` entry independently, so theorem-only
libraries are checked directly while importing sidecars do not re-run them.
Existing checked recursion remains on selected functions, while unselected
callees receive only their contracts.

`--changed-since` uses the documented safe first-delivery fallback: an entry
with imports is rebuilt as its selected scope, with no incremental success
marker reused. It never treats an imported proof as selected. Precise
dependency-level invalidation remains follow-up work.

The former copied `mdtests/rb_insert_color.md` fixture is now
`examples/rbtree-insert`. Its unchanged C and current proof attempt are in
`rb_insert_color.c` and `rbtree_insert.frontier`; both use the single shared
`examples/rbtree-model/rbtree_model.click`. The normal entry intentionally
selects no insert claim, and a dedicated negative regression requires the
frontier to continue failing at statement 23, so this conversion does not
misstate C3 as complete.

Regressions cover transitive generic algebraic/function/theorem/predicate/
resource imports, imported-theorem and callee-contract assumptions, explicit
library selection failure, exact file/location selection, proof cycles,
import cycles and diagnostics, ownership/collisions/capture, prepared and
source C inputs, tooling consistency, artifact invalidation, the conservative
incremental fallback, and deterministic chain/diamond/shared-library/proof-body
scaling.

Concrete handoff: retain this issue for the three requirements below. Extend
the same resolved graph and selection metadata to named contracts and external
C specifications first; then split `stdlib/prelude.click`; finally replace the
conservative imported-entry fallback with precise import-aware change
selection. Do not create a parallel include mechanism or proof cache.

## Follow-up scope retained by this issue

The first delivery is a coherent milestone, not completion of all module work.
Keep this issue open until the retained requirements are implemented or the
user explicitly reschedules them:

- Import shared named contracts and supported external C specifications without
  changing their checked semantics or silently selecting executable targets.
- Split `stdlib/prelude.click` using the same module mechanism; do not introduce
  a separate unchecked Rust-only include convention.
- Complete precise import-aware incremental and `--changed-since` selection,
  so unrelated targets are not rebuilt unnecessarily.

Aliases, qualified surface names, visibility controls, package management,
named CLI selectors, and persistent proof caching are not required to close
this issue. No new issue files are authorized by this handoff.
