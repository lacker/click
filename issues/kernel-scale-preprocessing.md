# Import kernel-scale preprocessed translation units

Priority: P2. The user confirmed on 2026-09-10 that the delivered importer
milestone is sufficient for MVR. Remaining full-Linux import coverage is deferred
and does not block MVR; this issue stays open for that work.

Found by the 2026-09-04 minimum-viable-rbtree (MVR) audit of Linux
`lib/rbtree.c` and its public headers. Expanded into an implementation handoff
on 2026-09-10, based on repository commit
`7103cbc6980eb8ea547a6f58322a26aba2b1bf40`.

## Handoff status and ownership

This document is the self-contained handoff to an Astra coordinator on another
machine. The user wants Astra to do investigation, planning, semantic decisions,
and milestone review, with Luna agents doing most implementation. The receiving
Astra may delegate bounded work to Luna agents. It should remain involved at
the review checkpoints below; the document is durable shared context, not a
claim that all design questions have already been resolved.

The original handoff contained repository inspection and planning only. The
receiving investigation has now captured a concrete Linux input; see the
progress section and `design/kernel-import-stage0.json`. This evidence does not
establish that Click supports that translation unit or that the importer is
complete. Do not treat illustrative interface names or suggested fixture
locations below as existing APIs or completed work.

Read the current `AGENTS.md`, this document, and the referenced implementation
before starting. The repository may have advanced; use symbol names to locate
code rather than assuming line numbers or this baseline are current. Update
this document with concrete decisions, evidence, and completed stages as work
proceeds. Do not create additional issue files or list entries without an
explicit user request. Move lasting design documentation out of this issue
before closing it under the repository issue policy.

## Problem and violated invariant

Click's source-bundle preprocessor intentionally supports a bounded subset:
project-local includes, a modeled `<stdint.h>`, object replacements including
expressions, strings, and aliases, bounded conditionals, and ordinary
function-like substitution with at most three parameters. The earlier version
of this issue described object macros as literal-only; that limitation has
already been relaxed. Some target predefines and bounded rescanning also exist.
These improvements do not establish agreement with a configured compiler.

Linux rbtree depends on a configured include graph, compiler predefines,
complex macro expansion, and generated build inputs. Reimplementing a growing
subset of the preprocessor inside Click risks verifying a different program
from the one selected by the actual build.

The C declarations and function bodies Click verifies must be the same active
translation unit selected by the configured compiler, except for an explicitly
checked, semantically harmless metadata projection. Unsupported preprocessing
must not force edits to upstream C or silently select another conditional
branch. A proof for configuration A must not be presented or reused as a proof
for configuration B without validating the new import identity.

## Scope and expected design impact

MVR targets one pinned Linux revision, compiler/toolchain, configuration, and
`x86_64-linux-kernel` target. This is a faithful source-import boundary for that
single configuration. Supporting a compiler/ABI matrix belongs to
[multiple-compilers.md](multiple-compilers.md).

The intended pipeline is:

```text
unchanged source + configured headers + pinned compiler/build inputs
    -> compiler preprocessing
    -> validated expanded C artifact + manifest + original-source map
    -> checked metadata classification, C parsing, and C lowering
    -> existing bounded verification and independent kernel checking
```

Retain the existing source-bundle mode for current fixtures. Add an explicit
compiler-backed import mode; never silently fall back between modes. Importing
preprocessed text must bypass the miniature macro expander and its synthesized
predefines. Do not preprocess the compiler's output a second time.

No new proof tactics, resource constructs, or logical axioms are expected.
Prefer project/import configuration over new Click proof syntax, retaining
`verifying "file.c";` as the logical source selection where practical. The
coordinator must choose and document the exact configuration discovery and CLI
interface after inspecting the existing project loader; workers must not
independently invent competing interfaces.

This does require making validated build identity and source provenance
explicit frontend inputs and carrying import identity into verification-result
and incremental-reuse boundaries. Additional C syntax or execution rules may
be necessary for actual expansions; those are separate, justified semantic
changes, not permission to erase syntax until parsing succeeds.

Preprocessing remains a trusted source-selection dependency: reproducing a
compiler invocation is not a formal proof of the compiler's preprocessor.
Click still independently parses and lowers executable C and checks proofs;
the compiler does not supply proof authority or executable semantics. Record
this distinction in the eventual user-facing import documentation.

## Current implementation landmarks and risks

Inspect these symbols at the receiving checkout before proposing edits:

- `src/languages/c/source.rs`: `ExpandedCSource`, `expand_includes`,
  `local_include_paths`, `kernel_primitive_for_macro`, and
  `object_macros_expand_expressions_strings_aliases_and_comments`.
  `ExpandedCSource` currently carries expanded text and a dependency set, not
  an original-source map.
- `src/surface/verification.rs`: `parse_c_source_unit`,
  `parse_verified_sources`, `c0_imported_headers`, and
  `c0_incremental_selection`. The source is expanded, then each dependency
  header is separately expanded and validated. Do not use that independent
  header interpretation for the compiler-backed path: inclusion macro state
  matters, and repeated expansion can cause excessive work.
- `src/source.rs`: `SourcePosition` currently holds line and column, without
  file identity. `src/languages/c/syntax.rs` uses those positions through
  tokenization, parsing, and lowered constructs. Source-map integration must
  reach downstream diagnostics, not just initial parser failures.
- `src/languages/c/syntax.rs`: `parse_translation_unit_for_source`,
  `validate_header`, `inline_function_kernel_name`, and
  `file_static_kernel_name`. Preserve translation-unit linkage identity
  independently of the original filename used for diagnostics.
- `src/languages/c/target.rs`: the single `CTarget::SUPPORTED` profile includes
  LP64 layout, unsigned plain char, and selected predefines. A target name
  alone is not validation of every compiler flag or implementation choice.
- `src/cli.rs`: `read_declared_sources` and `read_verifying_sources` load named
  source bundles. Inspect all CLI consumers before introducing a prepared
  import interface.
- `src/bin/click-verify.rs`: verification markers fingerprint the verifier,
  target, commit, sidecar, and switches; header discovery also appears here.
  External/generated inputs must not evade incremental invalidation.
- `mdtests/sequential_kernel_access_primitives.md`: current fixtures preserve
  names such as `READ_ONCE` and `WRITE_ONCE` for modeled lowering.

The macro primitive recognizer currently uses names and replacement-text
substring checks. Fully expanded compiler input loses those names and exposes
the implementation instead. This heuristic is not an equivalence certificate
for an arbitrary replacement body. Prefer modeling actual expanded constructs.
Any proposal to recover a primitive must establish checked equivalence,
including argument evaluation count, sequencing, qualifiers, and effects.
Do not use an overlay header or altered defines to replace upstream access
macros with verifier-friendly bodies.

Support for `typeof`, statement expressions, and `__builtin_expect` already
exists in the parser at the inspected baseline. Audit its actual coverage
against the pinned expansions instead of implementing from an outdated issue
inventory. Related documents may describe earlier slices rather than the
current code.

## Stage 0: establish the real input and resolve scope

Owner: Astra, with bounded Luna read-only investigation or capture assistance.
This stage precedes broad implementation delegation.

1. Find any existing MVR pin or capture work in the current repository. Reuse
   it if it satisfies the invariant. Otherwise choose one explicit upstream
   Linux commit, one exact toolchain, and a reproducible x86-64 configuration
   consistent with Click's supported target. Record why these were chosen.
   Do not choose or alter flags merely to hide an unsupported construct.
2. Obtain the actual build command for `lib/rbtree.c`, including generated
   configuration headers and forced includes. Derive preprocessing from that
   command using the selected compiler driver. Preserve flags that affect
   preprocessing, types, layout, or execution assumptions; document the
   removal of output/dependency-generation options. Do not guess an include
   list from the source. Verify that the unmodified input is accepted by the
   pinned compiler in its intended build environment.
3. Capture the complete preprocessed output with line markers, dependency
   evidence including system headers, compiler identity, command arguments,
   working directory, and controlled environment. Establish deterministic
   reproduction. Address location-dependent and time-dependent predefined
   macros without rewriting resulting C strings or tokens.
4. Inventory the actual output: rbtree functions and public inline bodies,
   required declarations and globals, GNU expressions/attributes/builtins,
   remaining directives, assembly, and proposed metadata omissions. Record
   exact original locations and small unmodified reproductions of blockers.
   Record bytes, tokens or lines, functions, and dependency counts for scale.
5. Use ordinary bounded parse/lower/verify entrypoints as appropriate to
   identify gaps. Do not expand tactics from an incomplete or failing proof.
   A diagnostic capture is not evidence that the target verifies. Keep
   incomplete experiments isolated; checked-in negative regressions should
   deliberately assert their diagnostic rather than leave failing examples.
6. Define the retained-input policy. The default retains all C, including
   inline bodies and storage. If complete header parsing exposes unsupported
   executable constructs, identify the needed semantic work; do not silently
   exclude unrelated-looking function bodies to meet this issue.
7. Record a concrete inventory and dependency order in this document, and
   finalize shared interfaces, manifest schema, fixture provisioning, and
   review criteria before launching implementation workers.

**Astra checkpoint A:** assess whether the selected configuration fits the
existing semantics and the no-storage-erasure criterion. Resolve the trust
boundary and API ownership. If it needs a fundamental scope change, explain
that to the user with the concrete offending input. Routine design choices
within this scope do not require another user permission round.

Stage 0 is a feasibility milestone, not an administrative prerequisite. The
complete header graph may require substantial new C semantics. Do not estimate
package 3 as a bounded importer change until the actual retained constructs
are inventoried. Start discovery with one or two read-only Luna assistants;
launch implementation workers only after checkpoint A.

## Manifest and reproduction contract

The first implementation should favor fresh, bounded preprocessing during
validation over a clever dependency cache. A manifest and an output hash alone
cannot prove that the output was generated from the declared inputs. A locked
import must reproduce and match the expected artifact before verification;
creating or refreshing the lock is a separate explicit operation. Changed
inputs must not silently refresh a lock during verification.

Choose a versioned serialized format using existing project conventions.
Specify required fields, duplicate/unknown-field handling, canonical encoding,
and collision-resistant content digests. The logical contents must cover:

| Input | Required identity or policy |
| --- | --- |
| Source | Logical translation-unit path, upstream revision, and exact content identity; revision alone cannot cover dirty or generated files |
| Toolchain | Compiler identity plus pinned executable/toolchain distribution identity covering relevant subprocesses and resource headers; version text alone is insufficient |
| Target | Supported Click profile, compiler target, and validated ABI/execution-affecting options |
| Invocation | Ordered argument vector, effective working directory, ordered include roots/sysroot, forced includes, defines/undefines, and expanded response-file contents |
| Environment | Explicit allowlisted values and a sanitized execution environment; account for include-search and reproducibility inputs |
| Filesystem inputs | Source, generated/configuration headers, project and system headers, and include-resolution identity, with logical roots mapped to local paths |
| Output | Exact preprocessed artifact digest and identity of any checked projection policy/version |
| Format | Manifest/import schema version and any compatibility version needed for reuse |

Record the original compile invocation as evidence as well as the derived
preprocessing invocation. Reject unsupported ABI-affecting options rather
than accepting them because the target is nominally LP64. This issue need
only validate one supported profile, not implement general target selection.

Dependency lists alone are insufficient: a newly created header earlier in an
include search path can shadow a previously hashed header; file-existence
conditionals can change output when a formerly missing file appears. Fresh
preprocessing checks these cases. Any later cache that skips preprocessing
must bind a complete immutable input/search environment or demonstrate an
equivalent validation scheme. Do not introduce that optimization in the first
slice without a concrete need and regressions.

Compiler output, source snapshots, and digest calculation must describe one
consistent input state. Use immutable/snapshotted inputs where possible;
otherwise detect concurrent input changes and reject/retry within bounds.
Do not hash one state and preprocess a different one. Avoid host path rewriting
that changes `__FILE__` values or other executable tokens. Source-root mapping
for diagnostics is separate from the identity of the actual compiler input.

Keep compiler launch at an owned external-tool boundary with an argument
vector, structured stdout/stderr capture, exit-status checks, bounded output,
and deadline/cancellation cleanup of its process tree. Never accept partial
output on compiler failure. Do not shell-evaluate command strings from a
manifest. A lock recording an invocation is not permission to execute arbitrary
build hooks. Fixture provisioning should be explicit and separately documented.

## Source maps, C semantics, and checked projection

Parse line markers as structured metadata, handling escaped filenames,
include entry/return, system-header flags, and compiler pseudo-files such as
`<built-in>` and `<command-line>`. Validate numbers and malformed markers.
Keep physical artifact offsets available for debugging. Do not interpret a
system-header marker as permission to ignore code or suppress Click errors.
Do not treat line markers as the authoritative dependency inventory.

The baseline promise is correct original file and line attribution. Ordinary
textual line markers do not supply full macro-expansion backtraces or exact
original columns inside a macro expansion. Report that limitation honestly;
do not manufacture precision. Reject or model residual semantic directives
such as packing pragmas rather than deleting all lines beginning with `#`.

Use an indexed source map shared by the prepared artifact. Preserve provenance
through tokens, AST nodes, lowering, and the diagnostic paths used by verify,
profile, audit, and expansion. Keep provenance separate from translation-unit
identity so a static inline function in one header can have different local
instances in different translation units without duplicate linkage names.

Every retained executable construct must have a modeled value, type, layout,
qualifier behavior, sequencing, and effect. Unknown attributes or builtins
must fail precisely. Integrate needed C support in small green changes with
unchanged source regressions. Existing modeled primitives must not conceal
extra effects in compiler expansions.

Default to no metadata projection. If Stage 0 establishes a need, define a
small structural classifier that recognizes the complete omitted construct
and checks its surrounding attachment/context. Give every accepted form a
semantic justification and a negative near-miss regression. An omission must
not change executable code, storage, initialization, type/layout facts,
linkage relevant to the program, or retained declarations' meaning.

An export record, section attribute, static object, constructor, or assembly
fragment is not harmless solely because it is called metadata. Do not use
regex deletion, filename allowlists, unknown-node skipping, or user-provided
assertions of harmlessness. A compiler AST dump may assist investigation, but
must not become unexamined authority for semantic erasure. If actual required
metadata has storage effects, retain/model it or escalate the conflict with
this issue's acceptance criteria. Preserve an auditable record of permitted
omissions with original locations and reasons, bound to the import identity.

**Astra checkpoint B:** review every semantic addition, primitive replacement,
and metadata-classification rule before integration. Passing positive tests
alone does not establish that the omission boundary is sound.

## Implementation packages and delegation

### Operating the work on the receiving machine

Use one persistent Astra high manager task as the user's point of contact.
That manager owns this plan, worker assignments, design decisions, review,
and integration. It spawns bounded Luna subagents rather than requiring the
user to manage a separate top-level task for every package. Keep worker
delegation under the manager; workers do not recursively spawn more agents
unless the manager explicitly assigns a justified independent subtask.

Begin implementation with two Luna medium workers, each in a dedicated worktree;
add a third only when a concrete independent assignment is ready.
Reuse a worker for related follow-up changes when its context remains useful;
retire it when its assignment is finished or unrelated new work needs fresh
context. The manager waits for results between decisions and reviews rather
than repeatedly rereading worker logs or duplicating their implementation.
One worker may own integration mechanics, but the manager retains acceptance
and semantic-review responsibility. Keep one serialized integration path.

The user can start the receiving manager with an instruction such as:

> Implement `issues/kernel-scale-preprocessing.md`. Act as the persistent
> Astra high coordinator, use Luna medium subagents for bounded implementation,
> and follow the document's discovery stages and review checkpoints. Keep the
> issue updated so the work can resume without this conversation. Handle routine
> coordination and green integration yourself; bring me scope changes and
> unresolved tradeoffs with concrete evidence.

Keeping the manager on high throughout is a practical default; changing to
medium for routine coordination is optional, not a required manual step.
The user should need to communicate with only the manager. If its context is
lost or it must move machines, resume from the updated issue, committed work,
and a compact record of active worker branches and outstanding assignments.

### Package boundaries

Use the following dependency order, refining ownership after Stage 0. The
interface names are descriptive, not required Rust type names. Prefer a shared
immutable prepared-import representation carrying expanded text, provenance,
dependencies, target, and validated identity. It should be constructed only
through validation paths; raw caller-supplied text plus a digest must not gain
validated-import status. Keep filesystem/compiler orchestration separate from
pure parsing/checking so library users and fixture gates can share the engine.

| Package | Owner and prerequisites | Deliverable |
| --- | --- | --- |
| 0. Capture and design | Astra; bounded Luna assistance | Actual pinned output inventory, settled import contract, task boundaries, and fixture/bootstrap plan |
| 1. Manifest and compiler adapter | Luna after checkpoint A | Lock creation and validation, controlled compiler invocation, mismatch diagnostics, bounded failure behavior |
| 2. Provenance | Luna after the shared artifact interface is fixed | Line-marker decoding, indexed mapping, propagation to C and proof diagnostics, linkage-preserving regressions |
| 3. Required C forms/projection | Narrow Luna assignments after inventory; Astra semantic review | Modeled constructs or justified checked omissions with positive and negative tests |
| 4. Project and reuse integration | One Luna integration owner after interfaces stabilize | One shared prepared-import route for verification tools, target/result identity, safe incremental invalidation |
| 5. Pinned regression and scale | Luna after packages 1-4; fixture preparation can start earlier | Real rbtree import/lowering gate, focused proof coverage, deterministic scaling, documented reproducible setup |
| 6. Final review and integration | Astra with one integration owner | Reviewed coherent green commits, documented limits, full gate evidence, issue closure only when complete |

Packages 1 and 2 can run concurrently after their interface is fixed. Package
3 can run alongside them only with separate owned files or clearly separated
commits; multiple workers editing `syntax.rs` indiscriminately is not a useful
swarm. Package 4 owns shared call-site edits. Start with two or three Luna
workers and increase only where work is independent and the machine can run
the builds without resource contention.

Before broad parallel implementation, assign one owner a minimal working route
from compiler preparation through parsing and independently checked verification
of the focused fixture. Use that route to validate the prepared-import interface
and mode selection. It is an intermediate milestone, not evidence that the
complete pinned Linux translation unit imports successfully.

Packages are dependency groups, not single worker-sized assignments. Split
package 1 into manifest validation, bounded compiler process ownership, and
toolchain/input reproduction changes with explicit intermediate contracts.
Split package 2 into line-marker indexing and downstream provenance propagation.
Each slice must be reviewable and green independently; keep incomplete wiring
in the task worktree until its tests establish coherent behavior.

The manager schedules expensive builds and full gates. The existing unit gate
may occupy every core, so workers must request a gate slot before starting a
full run; queue those runs instead of allowing competing gates to distort
timeouts. Focused checks can overlap when resource use is modest. This changes
scheduling only: every required green-commit gate still runs, including the
assembled integration gate.

Each worker assignment must state: baseline commit, worktree/branch, owned
files and symbols, prerequisite interfaces, concrete behavior, forbidden
shortcuts, required tests, and return format. Each worker returns a green
commit, changed-file summary, exact check commands and exit statuses, unresolved
questions, and any deviations. No worker integrates into the primary checkout.
The integration owner assembles reviewed commits in a task worktree and runs
the full gate there before moving a tested commit into the clean primary
checkout. Follow `AGENTS.md` when the base moves or conflicts occur.

Workers may decide routine implementation details within the agreed contract.
Return to Astra when evidence invalidates that contract, a new semantic rule
or projection is needed, an API change affects another package, a target/input
assumption changes, or a repository-defined tooling/scaling failure occurs.
Do not silently weaken tests, specialize upstream C, broaden an omission
allowlist, or repeatedly retry an unproductive approach. Astra should review
compact evidence and diffs, not supervise every edit or consume raw test logs.

Suggested operating choice: Astra high for initial design, semantic exceptions,
and final soundness review; Astra medium can handle settled coordination.
Luna medium is a reasonable starting point for bounded implementation; use
high for a difficult local change or review, and return architectural ambiguity
to Astra. These are workflow recommendations, not measured guarantees for this
repository. Do not spend maximum effort on every routine step by default.

## Required regressions and verification workflow

Use the shared bounded engine directly from CLI tools and fixture gates. Do
not build the import workflow by recursively spawning Click commands, hidden
child modes, test-binary wrappers, or stderr scraping. The external compiler
invocation is the explicit preprocessing dependency, not an excuse to add
nested verifier processes.

The focused compiler-backed fixture must be self-contained and exercise a
macro with more than three parameters, token pasting, nested rescanning, a
compiler predefined condition, and a system include selected from configured
include roots. Assert meaningful resulting C behavior and a checked proof,
not just that the output contains an expected string. Include a variant
whose selected branch changes with a define.

Required negative and integration coverage:

- Changed source, project header, generated header, system/resource header,
  define/undefine ordering, include-root ordering, forced include, response
  file, toolchain identity, target/ABI option, and artifact bytes reject an
  existing incompatible lock before proof execution.
- Header shadowing and changes in file-existence conditions cannot reuse stale
  output. Unsupported schema, malformed fields, and invalid line markers
  produce concise diagnostics. A supplied digest cannot bless forged output.
- Compiler nonzero exit, missing tool/input, output bounds, cancellation, and
  timeout cannot yield a validated artifact. Confirm child-process cleanup
  after interruption; do not trust later timing with stale workers.
- Errors in both the main C file and an included header map to original files
  and lines, including one error that occurs after parsing during lowering or
  verification. Nested includes and macro-generated constructs retain useful
  attribution without claiming nonexistent column precision.
- A header included under two distinct translation-unit macro states retains
  the correct separate inline bodies and internal-linkage identities. Source
  origin must not merge those instances. A header requiring prior macro/type
  context is not independently reinterpreted.
- Actual expanded access primitives preserve argument evaluation count,
  source-order effects, and modeled volatile behavior. Add adversarial cases
  with an extra write/call or changed replacement body so primitive-name
  recognition cannot mask behavior in the new import path.
- Every permitted metadata omission has an accepted exact form and rejected
  near misses involving storage, effects, semantic attributes, or changed
  declaration attachment. No projection is also an acceptable design if the
  full input can be modeled.
- Incremental markers/results cannot survive changed external import inputs
  by relying only on the Click repository commit. Safe conservative full
  invalidation for changed import identity is acceptable initially. Verify,
  profile, audit, and expand select the same prepared program.

The pinned regression must reproduce and import the actual unchanged
`lib/rbtree.c` plus public inline implementations reached through its headers.
Check the expected function/declaration inventory from Stage 0 and successful
parsing/lowering of the retained input, not merely a successful compiler `-E`
exit or one extracted helper. Preserve exact upstream source references and
original-source diagnostics. This issue does not require all final red-black
invariant proofs; those remain the broader MVR work. The focused compiler-backed
proof establishes the end-to-end verification route, while the pinned import
regression establishes coverage of the real source boundary.

Make fixture provisioning reproducible on the receiving machine and in CI.
Choose checked-in unmodified dependencies or a content-pinned prepared fixture
bundle/toolchain with documented bootstrap and provenance/license information.
Record that decision after Stage 0. Keep downloads out of `scripts/check.sh`;
bootstrap prepares required inputs separately. The gate must actually exercise
the pinned regression and clearly fail on missing prerequisites, never silently
skip it. A checked-in `.i` with no source/toolchain reproduction check does not
meet the invariant. Keep artifact-only parser tests distinct from the full
reproduction gate.

Read `docs/internals/verification-efficiency.md`. Share immutable input and
maps; do not clone complete translation units per function, re-expand every
header, or hash whole artifacts per tactic. Perform content validation once
per prepared import and reuse stable identities within the run. Add
deterministic scaling tests over at least N, 2N, 4N, and 8N for relevant axes:
expanded input size, header/declaration count, and functions sharing one import.
Count work at preparation/mapping/parsing boundaries; compiler wall time is
supporting evidence, not proof of the checker's scaling law. Preserve bounded
compiler resource behavior separately.

Run focused positive/negative tests for each package and the required full
`scripts/check.sh` gate for green commits, following `AGENTS.md`. Decide status
from the unpiped command's exit code. Ordinary verification comes before
profiling/expansion. Once a focused proof verifies, exercise expansion and
reverification plus profile/audit consistency through the shared engine; do
not claim that a successful parse proves certificate correctness. If tooling
fails, reduce and fix it first or restore a green checkpoint and report the
blocker, without filing new issues automatically.

**Astra checkpoint C:** inspect the final diff against the invariant, including
negative tests and any scope deviations. Independently inspect the reproduction
and projection boundaries, source/linkage identity, and cache invalidation.
Confirm clean primary checkout and expected base before integration. A green
suite is necessary but does not replace this semantic review.

## Acceptance criteria

- A project can import compiler-preprocessed C from a reproducible manifest
  tied to exact source, compiler, target, include, define, and flag inputs,
  with controlled generated/environment inputs and validated output identity.
- Preprocessing handles the pinned Linux rbtree include graph and macro uses
  without changing upstream `.c` or headers or substituting verifier-only
  macro implementations.
- Diagnostics and proof locations map through line markers to original source
  and header paths, with documented macro-column limitations and unchanged
  translation-unit linkage identity.
- A mismatched or stale manifest/artifact is rejected before verification;
  verification-result and incremental reuse cannot hide a changed import.
- Preprocessing is not trusted for C execution semantics: Click still parses
  and lowers every retained executable construct.
- Declaration-only kernel metadata may be omitted only by a documented,
  checked projection that cannot remove executable code or storage effects.
- Focused positive/negative regressions, the reproducible pinned rbtree import
  regression, required deterministic scaling checks, and `scripts/check.sh`
  pass. Required fixture/toolchain absence is not a passing skip.
- Lasting usage, trust-boundary, provisioning, and supported-semantics
  documentation is committed before this issue and its README entry are
  removed. Broader MVR proof completion is not implied by closing this issue.

## Progress for the receiving coordinator

Execution started on 2026-09-10 from
`fec5ada408f994369dd2e8c244a575542cc97d30`. The coordinator worktree is
`/tmp/click-kernel-scale-preprocessing`, branch
`codex/kernel-scale-preprocessing`. Stage 0 has two Luna medium investigations:
existing input/capture and provisioning evidence; shared engine/import API and
diagnostic integration. The first importer milestone is implemented below;
`scripts/check.sh` is its combined verification gate.

### Checkpoint A: captured input and approved first milestone

The user approved delivering the validated importer first on 2026-09-10, with
explicit rejection of unsupported C forms and compiler options. Full Linux
support and the original acceptance criteria above remain open. Completing this
first milestone must not close this issue or claim the real rbtree input lowers.

The pristine source is Linux `v6.8.12`, peeled commit
`632428373bea7581869cb05dce40bef0d37793e3`, from the kernel.org release archive
with SHA-256
`19b31956d229b5b9ca5671fa1c74320179682a3d8d00fc86794114b21da86039`.
This fixed release provides a reproducible discovery target; it is not a claim
to support a kernel-version matrix. A fresh `x86_64_defconfig` was built with
GCC `13.3.0` (Ubuntu `13.3.0-6ubuntu2~24.04.1`). Normal Kbuild compilation of
unmodified `lib/rbtree.c`, including objtool validation, exited 0. Missing host
build tools were provisioned under `/tmp`; no target compiler flags were changed.

The exact compiler argument vector, derived preprocessing vector, configuration,
compiler binary identities, and 222 concrete dependency hashes are recorded in
[`design/kernel-import-stage0.json`](../design/kernel-import-stage0.json).
Two preprocessing runs in an environment cleared to the recorded allowlist
produced identical bytes: 637,604 bytes, 16,371 lines, 1,552 line markers, SHA-256
`19a1f6aee08bc6b0b4e5c0f8959cf986da569547a227db2241974b5e446173e7`.
Line-marker filenames are not the dependency inventory. The live source/build
tree is `/tmp/click-linux-pinned`; captured output is
`/tmp/rbtree-v6.8.12-controlled-a.i`. The evidence JSON is an investigation
record, not a validated importer lock or a complete toolchain distribution.

The first ordinary parser rejection after decoding only structured line markers
is `include/linux/panic.h:12`, the variadic declaration of `panic`. Further
retained forms include `_Generic`, attributes, anonymous aggregates, and
effectful x86 assembly. Concrete examples include `cli` in
`arch/x86/include/asm/irqflags.h:37`, and export-generated pointer storage plus
`.export_symbol` assembly at `lib/rbtree.c:415` (and eleven further exports).
Neither disabling interrupts nor allocating export storage qualifies as harmless
metadata. The actual compiler vector also includes options such as
`-ftrivial-auto-var-init=zero`, `-fshort-wchar`, and `-fno-strict-overflow` that
require explicit target-policy review. Do not remove those options to make the
kernel input fit the first importer profile.

The earlier `/tmp/linux-6.8.12` tree and `/tmp/rbtree-6.8.12.i` combined upstream
sources with host-generated headers and failed compiler validation. They are
rejected exploratory inputs and must never be used as fixtures. A temporary
objtool-skipping build was also superseded by the successful normal build.

First-milestone interface decisions:

- Compiler imports are selected by explicit `<sidecar>.import.json` configuration;
  legacy source-bundle inputs remain available with no silent fallback.
- `click import lock <sidecar.click>` explicitly creates or refreshes the separate
  `<sidecar>.import.lock.json` and configured artifacts. Verification reproduces
  and validates the locked input without modifying it.
- Opaque `PreparedCImport` values carry validated text, source map, logical source
  identity, and import identity through the shared engine. Raw text plus a digest
  cannot manufacture this status.
- The initial importer accepts one explicitly checked GCC/x86-64 profile and a
  restricted argument vocabulary. Unsupported response files, compiler plugins,
  target options, residual directives, and C forms fail explicitly.
- Imported projects initially reject incremental `--changed-since` requests and
  do not read or create verification markers. Ordinary verification, profiling,
  audit, and expansion use the same validated prepared inputs.
- No metadata projection is authorized. The focused fixture establishes the
  compiler-backed proof route; kernel capture remains negative discovery evidence
  until the retained semantics and complete reproducible fixture gate are ready.

- [x] Repository inspection and handoff plan written at the baseline above.
- [ ] Stage 0: concrete pin, reproducible capture, inventory, and checkpoint A.
- [ ] Manifest/compiler adapter and source-map interfaces fixed and implemented.
- [ ] Required C forms/projection reviewed at checkpoint B and implemented.
- [ ] Shared project/tool integration and safe incremental identity completed.
- [ ] Focused, pinned, scaling, and full gates completed.
- [ ] Checkpoint C, durable documentation, and coherent integration completed.

When updating progress, record commit IDs, fixture/manifest paths, chosen
compiler/configuration identities, check results, and remaining blockers.
Do not replace unknowns with assumed success or mark the whole issue complete
because one implementation package landed.

## References

- [Multi-function files and headers](multi-function-files-and-headers.md)
- [GNU C extensions](gnu-c-extensions.md)
- [Multiple compilers and targets](multiple-compilers.md)
- [Linux rbtree inline helpers](linux-rbtree-inline-helpers.md)
- [Testing and tooling failure workflow](../docs/internals/testing.md)
- [Verification efficiency contract](../docs/internals/verification-efficiency.md)
- [GCC preprocessing options](https://gcc.gnu.org/onlinedocs/gcc/Preprocessor-Options.html):
  ordered `-D`/`-U`, forced includes, preprocessing output, and complete versus
  user-only dependency generation. Consult the pinned compiler's own version
  of the documentation during implementation.
- [GCC line-marker format](https://gcc.gnu.org/onlinedocs/cpp/Preprocessor-Output.html):
  file/line attribution, include flags, and directives that can remain in
  preprocessed output.

### First importer milestone

The implementation uses `languages::c::compiler_import::{create_lock,
load_imports}` and opaque, shared `PreparedCImport` values. The public command
is `click import lock <sidecar.click>`; the usage, restricted compiler profile,
resource limits, trust boundary, and provisioning requirements are documented
in [the import reference](../docs/reference/cli/import.md) and
[testing documentation](../docs/internals/testing.md#compiler-import-fixtures).

Compiler artifacts are freshly reproduced from controlled GCC arguments and
environment. Validation binds compiler/cc1/resources, the ABI probe, exact used
dependencies (including system headers), ordered source options, source bytes,
and output bytes. Before/after input snapshots catch concurrent changes;
ambiguous roots and unsupported arguments fail explicitly. A proof result
carries a fixed-size identity of the complete selected prepared project.
Imported incremental verification is rejected and verification markers are
bypassed. Proof tools retain the typed input, and compiler line markers supply
original file/line diagnostics through parsing and lowering. No metadata
projection or kernel primitive replacement is introduced.

The small checked-in fixture is `tests/fixtures/compiler-import/`; its direct
shared-engine gate is `tests/compiler_import.rs`. It covers contextual headers,
macro rescanning and token pasting, alternate definitions, configured system
headers, newly selected optional headers, tampering, cross-translation-unit
identity, lowering diagnostics, unsupported directives and retained assembly,
and checked expansion/reverification. It requires installed GCC and creates
fresh temporary artifacts; it does not download or silently skip prerequisites.
Deterministic multi-size checks cover actual line-marker decoding/lookup,
root snapshots, translation-unit caching, and functions sharing one import.

The complete Linux input and its original acceptance criteria remain open.
The discovery evidence still does not constitute a passing Linux fixture.
