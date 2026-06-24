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

## Design Principles

- Keep the three-language model clear:
  - **Kernel Click** is pure, explicit, and has no ambient C state.
  - **Surface Click** is the user-written proof/specification language.
  - **C fragments** are pieces of C syntax embedded in Surface Click and
    elaborated into Kernel Click.
- Prefer standard-library Click definitions over new kernel concepts when a
  feature is a named function or predicate.
- Add kernel support for general proof patterns: memory access, frames,
  arithmetic normalization, fold/range reasoning, aliasing, and modular calls.
- Every new proof feature should land with an mdtest that explains why it
  exists.
- Keep replayability in mind. `auto` may search, but successful automation
  should move toward stable proof steps when a proof becomes important.
- Diagnostics are a design surface. A failed proof should point at the missing
  requirement, invariant, frame fact, or unsupported C feature.

## Milestone 0: Keep The Current Core Coherent

Current status: mostly done, but this remains a maintenance milestone.

What exists today:

- C0 symbolic execution for `int32`, `uint8`, pointers, local arrays, memory,
  function calls, and annotated loops.
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
- A fresh agent can read `docs/README.md`, run an mdtest, and identify where a
  C0, Surface Click, Kernel Click, or stdlib change belongs.

## Milestone 1: Make C0 Big Enough For Real Library Kernels

The next C work should be driven by small real-library examples, not by trying
to clone C all at once.

Likely additions:

- C operators needed by ordinary library code:
  multiplication, division/remainder, shifts, bitwise operations, increments,
  compound assignment, ternary expressions, and `for` loops lowered to `while`.
- More integer types:
  `int`, `size_t`, `ssize_t`-like signed sizes, `uint32`, `uint64`, and
  well-specified casts/promotions.
- `char` and string literal support:
  null-terminated byte arrays, read-only static storage, and byte/string
  predicates in the standard library.
- Structs and field access:
  enough layout to model common library state objects without pretending a
  struct is an untyped blob.
- Enums and named constants:
  needed for real error codes and option flags.
- Globals:
  especially immutable global tables and string constants.

Design notes:

- Add types only when their undefined behavior, conversion, and comparison
  rules are explicit in Kernel Click.
- Prefer lowering sugar, such as `for`, into already-understood C statements.
- Keep byte widths on memory access obligations. Do not infer them only from
  pointer syntax.

Done means:

- We can transcribe or parse small real C helper functions without changing
  their control flow beyond harmless C0 desugaring.
- mdtests cover each new C feature with both a successful proof and at least
  one representative failure.

## Milestone 2: Heap, Ownership, And Real Frames

json-c-shaped code allocates, stores pointers inside objects, shares objects,
and releases them. Click needs a disciplined memory story before that is
comfortable.

Likely additions:

- Heap allocation and deallocation in the C semantics.
- Allocation predicates:
  valid object, valid byte range, initialized range, nullness, ownership, and
  maybe borrowed/shared access.
- Free/lifetime obligations:
  no use-after-free, no double-free, and no leaks for functions whose contracts
  promise ownership transfer.
- Struct-field frames:
  preserve fields or ranges not written by a function.
- Separation-style predicates:
  standard-library predicates for disjoint objects, object fields, byte strings,
  arrays, and maybe linked structures.
- Better alias diagnostics:
  failures should say which write might alias which old read or invariant.

Design notes:

- Do not make ownership a magic json-c concept. Build general memory predicates
  and then define json-c-specific predicates in a library spec.
- Treat `malloc`, `free`, `memcpy`, `memcmp`, `strlen`, and friends as either
  modeled builtins or externally specified functions, not as parser hacks.

Done means:

- We can verify memory safety for small functions that allocate, initialize,
  read, and free heap objects.
- Function contracts can express ownership transfer and frame preservation
  without exposing raw kernel internals to the user.

## Milestone 3: Proof Language And Standard Library Maturity

The current proof language can prove useful examples, but real libraries need
more reusable specifications and more predictable proof scripts.

Likely additions:

- Broader existential proof scripts:
  more source forms beyond requirements and better diagnostics for failed
  witnesses.
- More complete range combinators:
  `.all`, `.any`, `.fold`, `.map`-like derived definitions, and standard lemmas.
- Lemma declarations:
  reusable pure Click theorems over functions and predicates.
- Explicit rewrite/calc steps:
  better than hiding all proof search inside `simp`.
- Predicate/function namespaces that scale with modules.
- A richer standard library:
  integer ranges, more byte-slice predicates, null-terminated strings,
  permutations, sortedness, ownership predicates, and frame predicates.
- A clearer split between:
  executable C behavior, pure Click functions, predicates, lemmas, and proof
  tactics.

Design notes:

- Keep `function` for pure Click functions returning C-shaped values.
- Keep `predicate` for propositions.
- Put domain vocabulary in stdlib/spec files unless the kernel needs a general
  reasoning rule.

Done means:

- The same library predicate can be reused across multiple functions without
  copying proof scripts.
- Common range/string/frame facts are proved by named stdlib lemmas or stable
  proof steps, not by adding ad hoc special cases every time.

## Milestone 4: Modular Verification At Library Scale

A real library cannot be verified as one giant symbolic execution.

Likely additions:

- Separate function summaries that can be checked once and reused.
- Verified external function specifications for libc and library-local helpers.
- Module/import support for Click specs and stdlib files.
- Stable naming for proof artifacts and generated obligations.
- Incremental verification:
  rerun the affected functions/specs, not the whole world.
- Counterexample-oriented failure output:
  path conditions, failing memory cell, missing bound, missing disjointness, or
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

## Milestone 5: Real C Frontend Strategy

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

## Milestone 6: json-c-Shaped Pilot

The pilot should be narrow but real. Pick a small, stable subset of a real C
library and verify it end to end.

Candidate target properties:

- Memory safety for selected constructors/destructors.
- Correct behavior for selected getters/setters.
- String or byte-buffer invariants for selected parsing/printing helpers.
- Reference-count or ownership invariants for a small object lifecycle.
- Frame properties: a setter changes the intended field and preserves the rest.

Suggested order:

1. Vendor or point at a frozen target snapshot.
2. Select 3-5 small functions that exercise pointers, structs, strings, and
   helper calls.
3. Write sidecar specs with explicit preconditions and ownership/frame
   predicates.
4. Add the smallest missing C0/frontend and proof features needed by those
   functions.
5. Verify memory safety first.
6. Add functional postconditions once memory safety is stable.
7. Document every reusable predicate or lemma in the standard library docs.

Done means:

- The repository contains a repeatable command that verifies the pilot.
- The pilot proves at least one property that would be meaningful to a C
  maintainer, not just a toy arithmetic fact.
- The docs explain the proof architecture well enough that a fresh agent can add
  the next function from the same library.

## Near-Term Work Queue

Good next tasks from the current state:

1. Add more fold/range lemmas beyond alpha-equivalent folds and the current
   count-shaped split rules.
2. Decide the null-terminated string abstraction, then add string predicates on
   top of the byte-slice prelude. Open questions include whether the primary
   predicate is exact-length, bounded-by-max, offset-based, or some combination,
   and how explicit guarded propositions should lower partial C fragments.
3. Add C multiplication and simple bitwise operators with overflow/definedness
   tests.
4. Add structs and field loads/stores in the smallest form needed by a pilot.
5. Model a tiny heap API or externally specified `malloc`/`free`.
6. Improve failure output for missing loop invariants and alias/frame facts.
7. Create a `third_party/` or `examples/real/` pilot area with a frozen
   json-c-shaped target function.

Use the feature playbook for each item: start with a failing mdtest or pilot
test, make the minimal design change, update docs, then run the full suite.
