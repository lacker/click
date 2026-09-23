# An uncaught throw leaves the function without running its destructors

P1. Every Throw outcome that crosses a frame boundary carries the memory
effects of each live nontrivial destructor, newest first — that is C++'s
unwinding, not a cleanup-side nicety.

## What was found

`CppStatement::Throw` lowers to a bare `CStatement::Throw` with the artifact's
`Throw` variant having no cleanup chain (`src/languages/cpp/schema.rs:338`),
`validate_return_cleanups` explicitly skips `Throw`
(`schema.rs:2041`), the throw edge's state export retires the frame through
`end_function_body_automatic_lifetimes`
(`src/kernel/functions.rs:20933`, `20012-20030`) without running any
destructor, and the exporter emits no throw cleanups either. So a function
whose body ends with a live destructible in a Throw path *exports a
knowledge-complete join* under a state in which none of the enclosing
destructors ran — both mis-modeling and a false-acceptance direction for
the caller's facts.

Reachable shapes (both pass schema validation today; the explicit schema
note permits one outer destructible followed by one inner cleanup scope at
`schema.rs:1295-1305`):

```cpp
struct Restore { int* pointer; int saved;
  explicit Restore(int* slot) noexcept : pointer(slot), saved(*slot) { *pointer = 9; }
  ~Restore() noexcept { *pointer = 42; }
};
int f(int& v) {
    Restore guard(&v);
    if (v > 0) { throw 7; }   // validate_return_cleanups skips Throw
    return v;                 // last statement is Return -> validation passes
}
int g(int& a, int& b) {
    Restore outer(&a);
    { Restore inner(&b); helper(true); }  // inner handler runs ~inner, rethrows
    return a;                              // rethrow escapes: ~outer never runs
}
```

Every mdtest wraps its guard in a `catch` (`mdtests/cpp_one_guard_unwind.md`
and siblings), so the uncaught propagation path is unexercised today. The
caught paths are sound: handler bodies execute as real kernel statements
(`src/languages/cpp/lowering.rs:358-383`, `417-550`), so their writes are
recorded, and the try-frame evidence walk pops only the top frame
(`src/kernel/proof/execution.rs:5361`).

Same root, promotion shape from a follow-up audit (weak-observation pass):
`statement_may_throw` (`src/languages/cpp/lowering.rs:917`) reports every
`Declare` as non-throwing, including `CppInitializer::Constructor` ones.
Constructor initializers reach a throwing callee in the exception-enabled
profile (Free functions may call/throw; the no-throw rule
`schema.rs:925-936` applies only to non-Free object operations), so a
*constructing* Declare inside a body with live destructibles is never
edge-wrapped and an initializer throw escapes without the unwind walk too.
Both shapes belong to the same invariant; the fixer should punish both at
one lowering point (every declare-with-throwable-initializer and every
throw inside a cleanup-living body carries the active prefix).

## Intended regression

Two mdtests on the shape above: the *true* C++ outcome
(`exceptional ensures v[0] == 42` — the destructor ran while unwinding out)
must verify, and the currently-accepting `ensures v[0] == old(v[0])` must
be refused once the unwind walk runs the enclosing destructors. The fix
locus is the schema/edge — emit the cleanup chain on throw edges the way
`lower_throwing_statement` already does per-statement for scopes — plus a
destructor-aware boundary walk at the throw export; the C sources stay
untouched.

## Acceptance

- [ ] Uncaught throw out of a frame with live destructibles runs (or
      records) the enclosing destructors newest-first, and both regression
      contracts above verify as stated.
- [ ] `scripts/check.sh` green.
