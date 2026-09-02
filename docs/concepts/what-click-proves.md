# What Click is

Click is a verifier for C-like code.

You write ordinary C0 source files, then write `.click` sidecar files that say
what the C functions are supposed to guarantee. Click checks those sidecars
against the C code.

The smallest mental model is:

```text
C source + Click sidecar -> verifier -> pass or diagnostic
```

Click is not a replacement for C. It does not compile your program, rewrite your
program, or ask you to move your implementation into a theorem prover. The C
function remains the thing being verified. The `.click` file is a specification
and proof layer beside it.

## Existing C comes first

A fundamental goal of Click is to verify existing C code, including code whose
control flow, helper boundaries, naming, or memory access patterns were chosen
without Click in mind. Requiring a large project to refactor working code before
verification would make adoption much harder and would hide exactly the proof
patterns Click needs to learn.

For C within Click's supported semantics, an inability to prove a true claim is
a limitation in the specification, proof language, verifier, or automation. It
is not a reason to add a no-op branch, route the operation through a special
helper, rename a local, or otherwise make the C more proof-friendly. The proof
may need more explicit contracts, invariants, resources, or lemmas; Click may
need a new general reasoning rule. The implementation being verified stays the
same.

There are narrow exceptions. A project may fix a real C bug or undefined
behavior, make a program change it wanted independently of verification, or
translate unsupported syntax into the C0 subset while preserving its semantics.
Those are program or frontend-boundary changes, not proof workarounds.

## What Click proves

A Click proof says:

- if the function is called in a state satisfying its `requires` clauses,
- no finite modeled execution reaches checked C undefined behavior, and
- if the function returns, its return state satisfies every stated `ensures`
  clause.

This is a partial-correctness guarantee. A C function may intentionally run
forever; an ordinary Click contract does not claim that it terminates. Loop
invariants prove safety across every finite number of iterations and describe
any exit that does occur.

The guarantee covers the modeled C0 execution and resources, not the physical
machine running the verifier or program. In particular, a verified function
can still exhaust the process stack, address space, or available memory; those
resource limits are outside the current judgment. C constructs outside C0's
model are rejected with a diagnostic rather than silently approximated.

For example, a Click contract can say that a function returns a particular
value, preserves part of memory, writes only a stated range, or maintains an
array property such as permutation.

Click also treats C undefined behavior as part of verification. If a function
can overflow signed `int32`, read invalid memory, or divide by zero under its
requirements, the proof should fail.

## The current C target

The current C subset is called C0. It is intentionally small: `int32`, `uint8`,
pointers, arrays, loops, function calls, and a pilot slice of structs. C0 exists
so the verifier can grow against precise semantics before it accepts more of
real C.

The long-term goal is to verify realistic C codebases. The current system is a
small but working path toward that goal.

## The main pieces

You will see these terms throughout the documentation:

- **C0 source**: the C-like implementation being verified.
- **Click sidecar**: a `.click` file containing contracts and proofs for C0
  functions.
- **Contract**: the `requires`, `ensures`, `immutable`, and `mutable` clauses
  for a function.
- **Proposition**: a logical claim written in Click, such as `result == x` or
  `forall (k: int32) { ... }`.
- **Proof clause**: the `by ...` part that tells Click how to prove a guarantee.

The basic workflow is to start from the C as written, write a contract, run
Click, and improve the contract, proof, or Click itself until the verifier can
justify the claim.
