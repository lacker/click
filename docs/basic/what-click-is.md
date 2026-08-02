# What Click Is

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

## What Click Proves

A Click proof says:

- if the function is called in a state satisfying its `requires` clauses,
- then every modeled execution path avoids the checked C undefined behavior,
- and every path satisfies the stated `ensures` clauses.

For example, a Click contract can say that a function returns a particular
value, preserves part of memory, writes only a stated range, or maintains an
array property such as permutation.

Click also treats C undefined behavior as part of verification. If a function
can overflow signed `int32`, read invalid memory, or divide by zero under its
requirements, the proof should fail.

## The Current C Target

The current C subset is called C0. It is intentionally small: `int32`, `uint8`,
pointers, arrays, loops, function calls, and a pilot slice of structs. C0 exists
so the verifier can grow against precise semantics before it accepts more of
real C.

The long-term goal is to verify realistic C codebases. The current system is a
small but working path toward that goal.

## The Main Pieces

You will see these terms throughout the book:

- **C0 source**: the C-like implementation being verified.
- **Click sidecar**: a `.click` file containing contracts and proofs for C0
  functions.
- **Contract**: the `requires`, `ensures`, `immutable`, and `mutable` clauses
  for a function.
- **Proposition**: a logical claim written in Click, such as `result == x` or
  `forall (k: int32) { ... }`.
- **Proof clause**: the `by ...` part that tells Click how to prove a guarantee.

The basic workflow is to write a contract, run Click, and improve either the
contract or the proof until the verifier can justify the claim.
