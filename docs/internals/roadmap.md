# Roadmap

This is the end-to-end roadmap for growing Click from the current C0 verifier
into a tool that can verify a meaningful slice of a real C library, such as
json-c. It is intentionally agent-facing: use it to decide what work to do next,
what design pressure a feature is supposed to satisfy, and when a milestone is
actually done.

The north star is not "parse all C" or "prove all mathematics." The north star
is:

> Click can verify memory safety and useful functional properties for selected
> functions in a real library, with enough local specifications that another
> agent can extend the proof without redesigning the system.

## Design principles

- **Verify the C as written.** Existing source is the adoption boundary. For C
  inside the supported semantics, do not change control flow, helper boundaries,
  redundant operations, local names, or other implementation details merely to
  make a proof pass. A true but unprovable claim is pressure to improve Click.
  C changes are acceptable only when independently desired, when fixing a real
  C bug or undefined behavior, or as documented semantics-preserving C0
  desugaring.
- Keep the three-language model clear:
  - **Kernel Click** is pure, explicit, has no ambient C state, and has no
    user-facing textual syntax.
  - **Surface Click** is the user-written proof/specification language.
  - **C fragments** are pieces of C syntax embedded in Surface Click and
    elaborated into Kernel Click.
- Prefer standard-library Click definitions over new kernel concepts when a
  feature is a named function or predicate.
- Add kernel support for general proof patterns: memory access, frames,
  arithmetic normalization, fold/range reasoning, aliasing, and modular calls.
- Every new proof feature should land with an mdtest that explains why it
  exists.
- Keep checkability in mind. `auto` may search, but successful automation
  should move toward stable tactics when a proof becomes important.
- Diagnostics are a design surface. A failed proof should point at the missing
  requirement, invariant, frame fact, or unsupported C feature.
- Surface Click is closed under tooling: expansion, profiling hints, and
  diagnostics emit only documented syntax accepted by the ordinary parser.

## Milestone 0: keep the current core coherent

Current status: mostly done, but this remains a maintenance milestone.

What exists today:

- C0 symbolic execution for scalar `int16`, `int32`, `uint8`, `uint16`, and `uint32`, named enum fields, pointers, local
  arrays, memory, function calls, annotated loops, and exact struct or
  runtime-sized `int32` allocation lifetimes.
- Surface Click contracts, loop invariants, memory effects, predicates, pure
  functions, `if`, `let`, `.fold`, `forall`, and selected range combinators.
- A small standard library with `count`, `permutation`, and initial byte-slice
  helpers over `uint8[]`.
- Kernel docs that distinguish Kernel Click, Surface Click, and C fragments.
- A kernel module split that keeps theorem construction inside `src/kernel/`.

Keep doing:

- Tighten the kernel API when refactoring. `Theorem` construction should remain
  inside the kernel.
- Avoid adding one-off kernel names for standard-library predicates.
- Maintain docs and mdtests in the same change as behavior.

Done means:

- `cargo test` is green.
- A fresh agent can read `docs/index.md`, run an mdtest, and identify where a
  C0, Surface Click, Kernel Click, or stdlib change belongs.

## Milestone 1: make C0 big enough for real library kernels

The next C work should be driven by small real-library examples, not by trying
to clone C all at once.

Likely additions:

- C operators needed by ordinary library code:
  ternary expressions, value-producing update expressions, and broader `for`
  forms beyond the current assignment/update lowering.
- More integer types:
  pointer/array forms of `size_t`, `ssize_t`, and `uint64`, and
  well-specified casts/promotions.
- Basic ASCII string literal support now lowers to null-terminated, read-only
  function-owned byte arrays; remaining work includes `char`, wider literal
  forms, and byte/string predicates in the standard library.
- Remaining static-storage work: other linkage forms, immutable global tables,
  and initialization ordering. Static scalar-field aggregates now accept
  out-of-order `.field = literal` designators, and their fixed-size
  one-dimensional arrays accept `[literal] = {...}` element designators with
  static zero fill. Fixed-size
  one-dimensional scalar global arrays now use stable cross-translation-unit
  or translation-unit-private storage with literal/zero element
  initialization. Fixed-size one-dimensional arrays of supported scalar-field
  aggregates now use the same stable linkage and ABI-sized element storage;
  non-literal designators, incomplete, multidimensional, and dynamically
  initialized aggregate tables remain open.
  Scalar file-scope globals now cover integer definitions, compatible `extern`
  declarations, one linked definition, shared state across calls, and contract
  footprints. File-scope scalar `static` objects now use
  translation-unit-qualified storage, while function-local scalar `static`
  objects use stable function-qualified storage; both support one-time
  literal/zero initialization and explicit contract footprints. Fixed-size
  one-dimensional scalar arrays are also supported for function-local statics;
  aggregate, multidimensional, incomplete, and dynamic-initialization cases
  remain open; zero-initialized and positional compile-time initialized
  scalar-field aggregate globals, aggregate arrays, and function-local statics
  now use the same stable typed-field storage model.
- Broader structs and field access: the current LP64 slice has multi-field
  declarations, alignment/tail padding, chained pointer-field loads/stores,
  field resource places, and nested leaf-field access through embedded
  aggregate places. One-dimensional function parameters declared as arrays of
  the supported structs now retain their ABI stride. Copyable by-value structs
  with scalar (including `uint32`, `int64`, and `uint64`), named-enum, fixed-dimensional scalar-array, and recursively embedded
  struct fields now have explicit fresh-copy semantics for parameters, locals,
  assignments, and returns; nested fields and array elements are copied
  recursively; fixed-dimensional arrays of embedded structs are flattened
  row-major to typed leaf fields with their complete ABI stride; data-pointer
  fields are shallow-copied with their pointee provenance shared. Modeled
  scalar leaf-field address-taking now preserves nested ABI offsets and
  allocation provenance, including row-major indexed cells in
  fixed-dimensional scalar-array fields. Remaining work includes struct values
  containing function pointers or unions and address-taking beyond modeled
  scalar leaves. Direct whole-struct lvalue loads and copies, including
  embedded aggregate assignment and aggregate arguments/returns, now lower to
  the same recursive typed leaf-copy machinery without a runtime aggregate
  value. Pointer-backed aggregate returns also support field-wise relational
  postconditions over mixed-width and nested fields while preserving fresh
  return storage. Positional initializers for copyable struct-valued locals
  recursively write typed leaves and zero-fill omitted members, including
  nested structs and fixed-dimensional scalar or embedded-struct arrays.
  Fixed-dimensional local arrays of copyable structs now accept nested
  positional element groups and zero-fill omitted fields and elements using
  the complete ABI-sized element stride.
  Conditional expressions over copyable struct values now use fresh
  address-backed temporaries and branch-local recursive copies; mixed-struct
  and union conditionals remain outside the model. Bitfields and other compiler-dependent layout rules are tracked in the
  multiple-compiler issue. Named
  enum fields
  and constants are supported, but enum parameters, returns, locals, arrays,
  and anonymous declarations remain outside the slice.
- Globals and statics:
  especially immutable global tables and string constants.

Design notes:

- Add types only when their undefined behavior, conversion, and comparison
  rules are explicit in Kernel Click.
- Prefer lowering sugar, such as `for`, into already-understood C statements.
- Keep byte widths on memory access obligations. Do not infer them only from
  pointer syntax.

Done means:

- We can parse small real C helper functions and verify their original
  behavior. Where the current frontend requires C0 desugaring, the translation
  is documented and semantics-preserving; proof convenience never justifies a
  source change.
- mdtests cover each new C feature with both a successful proof and at least
  one representative failure.

## Milestone 2: spec state, resources, heap, and real frames

json-c-shaped code allocates, stores pointers inside objects, shares objects,
and releases them. Click needs a disciplined memory story before that is
comfortable.

Likely additions:

- Resource and memory-permission logic:
  read/write authority over memory locations or ranges. A first mandatory
  viewed/owned resource context exists for memory ranges, including
  covered subrange transfer for function calls. The implementation now has an
  explicit internal resource-family boundary for the memory family plus
  exact-match declared resources whose equal owned units normalize to a
  quantity and transfer one unit at a time. Exact and wildcard population
  counts can be related to concrete state; the refcount example uses this for
  retain/release. It also has composite resources with explicit
  `unfold(resource)` and `fold(resource)` operations for wrappers over built-in
  resources, other declared resources, and resource facts. Fractions, persistent
  token resources, implicit unfold/fold search, custom resource-family algebra,
  abstract ownership predicates are still future work. The heap slice now adds
  exclusive allocation authority for structs, scalar buffers, and pointer
  arrays, complete-access checks for `free`, retired lifetimes, and leak checks
  at verified exits.
- First-class spec/model state:
  proof-only state that can be mentioned across program points if examples need
  arbitrary model variables beyond resources.
- Broader allocation beyond the modeled struct, scalar-buffer, and pointer-array
  forms: other unsupported allocator APIs remain. External contracts can now
  describe compatible typed data-pointer and pointer-array allocators. The
  current heap slice includes bounded typed and
  arbitrary-byte `realloc`, including preserved zeroed prefixes, plus the
  supported `calloc` forms.
- Richer initialization predicates when examples need to package partially
  initialized heap storage instead of storing every field before folding an
  object resource.
- Struct-field frames:
  preserve fields or ranges not written by a function.
- Separation-style predicates:
  standard-library predicates for separated objects, object fields, byte strings,
  arrays, and maybe linked structures.
- Better alias diagnostics:
  failures should say which write might alias which old read or resource fact.

Design notes:

- Do not make ownership a magic json-c concept. Build general memory predicates
  and then define json-c-specific predicates in a library spec.
- Do not design refcount ownership before spec state and basic resources are
  settled. Refcounting is a pressure test for those layers, not the starting
  point.
- Treat `malloc`, `free`, `memcpy`, `memcmp`, `strlen`, and friends as either
  modeled builtins or externally specified functions, not as parser hacks.

Done means:

- We can verify memory safety for small functions that allocate, initialize,
  read, and free heap objects.
- Function contracts can express ownership transfer and frame preservation
  without exposing raw kernel internals to the user.

## Milestone 3: proof language and standard library maturity

The current proof language can prove useful examples, but real libraries need
more reusable specifications and more predictable proof scripts.

Likely additions:

- Broader existential proof scripts:
  more source forms beyond requirements and better diagnostics for failed
  witnesses.
- More complete range combinators:
  `.all`, `.any`, `.fold`, `.map`-like derived definitions, and standard
  theorems.
- Richer theorem reuse:
  theorem application exists for stdlib and current-file pure proposition
  theorems; next slices should cover better diagnostics, named conclusion
  selection, and eventually separate reusable resource-rule forms if repeated
  unfold/fold patterns justify them.
- More reusable rewrite support: `rewrite(P)` and named theorem applications
  provide explicit checked steps; remaining work is better theorem
  selection and reusable algebraic lemmas rather than another calculation
  vocabulary.
- Predicate/function namespaces that scale with modules.
- A richer standard library:
  integer ranges, more byte-slice predicates, null-terminated strings,
  permutations, sortedness, resource/ownership predicates, and frame
  predicates.
- A clearer split between:
  executable C behavior, pure Click functions, predicates, theorems, and proof
  tactics.

Design notes:

- Keep `function` for pure Click functions returning C-shaped values.
- Keep `predicate` for propositions.
- Put domain vocabulary in stdlib/spec files unless the kernel needs a general
  reasoning rule.

Done means:

- The same library predicate can be reused across multiple functions without
  copying proof scripts.
- Common range/string/frame facts are proved by named stdlib theorems or stable
  tactic scripts, not by adding ad hoc special cases every time.

## Milestone 4: modular verification at library scale

A real library cannot be verified as one giant symbolic execution.

Likely additions:

- Broader modular summaries: verified Click function contracts are already
  checked once and used at calls, with dependency-ordered targeted
  verification. Remaining work is persistence/import across modules and richer
  invalidation boundaries.
- Verified external function specifications for libc and library-local helpers
  beyond the current same-project contract model.
- Module/import support for Click specs and stdlib files.
- Stable naming for proof artifacts and generated obligations.
- Incremental verification:
  rerun the affected functions/specs, not the whole world.
- Counterexample-oriented failure output:
  path conditions, failing memory cell, missing bound, missing separation, or
  unsupported syntax.

Design notes:

- Function calls should prefer verified summaries over inlining.
- Specs for external functions should be ordinary Click files when possible.
- Generated proof obligations should be readable enough that an agent can add
  the missing `requires`, `invariant`, `mutable`, or `unfold` step.

Done means:

- A directory of C files plus Click sidecars can be checked in a repeatable
  order.
- A changed helper only invalidates the proofs that depend on that helper's
  specification.

## Milestone 5: real C frontend strategy

The hand-written C0 parser is useful for design, but a real-library target
needs a plan for C as written.

Decision gate:

- Either continue expanding C0 as a strict verified subset and manually adapt
  target functions into it.
- Or add a frontend that consumes a real C AST, then lowers a supported subset
  into Kernel Click while rejecting unsupported constructs clearly.

Likely additions if we use a real frontend:

- Source spans from C into proof diagnostics.
- Preprocessor-aware inputs or a frozen preprocessed C mode.
- A lowering report explaining which C constructs were accepted, desugared, or
  rejected.
- A compatibility layer for typedefs, macros that become constants, and common
  compiler extensions.

Done means:

- The target library slice is checked from source that stays close to upstream
  C, and unsupported constructs fail with actionable diagnostics.

## Milestone 6: json-c-Shaped pilot

The pilot should be narrow but real. Pick a small, stable subset of a real C
library and verify it end to end.

Candidate target properties:

- Memory safety for selected constructors/destructors.
- Correct behavior for selected getters/setters.
- String or byte-buffer invariants for selected parsing/printing helpers.
- Reference-count or ownership invariants for a small object lifecycle, after
  spec state and resource logic are available.
- Frame properties: a setter changes the intended field and preserves the rest.

Suggested order:

1. Vendor or point at a frozen target snapshot.
2. Select 3-5 small functions that exercise pointers, structs, strings, and
   helper calls.
3. Write sidecar specs with explicit preconditions and frame predicates. Add
   ownership predicates only after spec state and resource logic are in place.
4. Add the smallest missing C0/frontend and proof features needed by those
   functions.
5. Verify memory safety first.
6. Add functional postconditions once memory safety is stable.
7. Document every reusable predicate or theorem in the standard library docs.

Done means:

- The repository contains a repeatable command that verifies the pilot.
- The pilot proves at least one property that would be meaningful to a C
  maintainer, not just a toy arithmetic fact.
- The docs explain the proof architecture well enough that a fresh agent can add
  the next function from the same library.

## Near-Term work queue

Good next tasks from the current state:

1. Choose the next spec/model-state boundary before adding fractional memory
   permissions or persistent resource views. Mandatory viewed/owned range resources, composite
   wrappers, and exact struct/runtime-sized `int32` allocation lifetimes
   already exist.
2. Broaden the struct/field memory model beyond compact C0 field lowering:
   whole-object resources, field-dependent composite resources, field
   frames, and eventually broader by-value shapes and ABI layout details.
3. Add more fold/range theorems beyond alpha-equivalent folds and the current
   count-shaped split rules, especially when the pilot or sorting/string tests
   expose a reusable proof pattern.
4. Extend the first C-string predicate layer toward a full string model. Open
   questions include first-class Click string values, libc function summaries,
   offset-based string slices, and whether/how higher-level predicates can
   package structural memory loadability instead of requiring separate
   `loadable` facts.
5. Extend the integer-promotion/conversion slice beyond the current `uint8`
   rvalue promotion, scalar `uint32` modular arithmetic and unsigned order,
   `uint8`-to-`int32` widening, and checked `int32`-to-`uint8` narrowing rules.
   The open design question is how much of C's usual arithmetic conversions
   Click should model next versus reject in C0 until the integer story is
   broader.
6. Use the allocated examples to guide broader allocator support beyond the
   current runtime-sized `int32` slice: retain definitional lifetime matching,
   separated survivors across `free`, and proof-local branching as explicit
   design requirements.
7. Improve failure output for missing loop invariants and alias/frame facts.

Use the feature playbook for each item: start with a failing mdtest or pilot
test, make the minimal design change, update docs, then run the full suite.
