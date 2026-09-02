# Support taking the address of a parameter

Found on 2026-09-01 while closing the termination-measure-aliasing issue.

`address_of_lvalue_paths` (`src/kernel/eval/expression.rs:617-639`) produces
`CRuntimeError::UnboundVariable` when `lvalue.pointer(state)` is `None`, and
it is `None` for every function parameter: parameters are bound as values
(`Variable(position)`, `src/surface/lowering/resource_lowering.rs:47-56`) and
have no `local:{name}` stack cell, unlike declared locals. So `p = &n;` for a
parameter `n` fails every proof at that statement with "unbound variable",
while the same statement on a local works (see
`mdtests/loop_rejects_stale_address_escaped_local.md`). Real C takes the
address of parameters routinely: passing `&n` to an out-parameter helper,
`scanf`-style fills, and swapping through pointers.

Because of this gap, the recursive form of the termination-measure aliasing
hole (`int32 f(int32 n) { int32* p; p = &n; if (n > 0) { *p = 1000; f(n - 1); }
return 0; }`) is not reachable from C source today. The kernel still rejects
it (`reject_address_escaped_measure` in `src/kernel/termination.rs`), covered
by a unit test on the walker; the end-to-end mdtest belongs here.

## Violated invariant

A parameter is an object with an address, exactly like a local. Taking its
address must yield a pointer to a cell that holds the parameter's value, so
that stores through the pointer are visible to later reads of the parameter
by name.

## Intended regression

```c
int32 through_pointer(int32 n) { int32* p; p = &n; *p = 5; return n; }
```

with `ensures result == 5 by auto;` must verify. Then add the termination
negative test:

```c
int32 f(int32 n) { int32* p; p = &n; if (n > 0) { *p = 1000; f(n - 1); } return 0; }
```

with `decreases n; ensures result == 0 by auto;` expecting
`fail: termination measure `n` in `f` has its address taken`.

## Acceptance criteria

- Parameters whose address is taken get a stack cell at function entry (or
  every parameter does, with a documented cost model), and reads of the
  parameter by name resolve through that cell after a store.
- Call-site argument binding, contract lowering of parameters, and loop
  havoc of address-escaped parameters (`address_escaped_scalar_locals`,
  `src/kernel/loops.rs`) all agree on the representation.
- Both mdtests above pass; `docs/reference/language/c0.md` documents the
  behavior; `scripts/check.sh` passes.
