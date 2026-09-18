# an unestablished conversion condition names the operation that may overflow

`to_integer(hi - 1)` also carries the definedness of `hi - 1`. That condition
used to print as `subtraction overflow is false`, which does not say which
subtraction of which statement, and the reader had no way to find out.

It now names the operation in the spelling the statement uses, and it says
truthfully that no premise reached this lowering at all.

```click
theorem endpoint_without_a_bound(hi: int32) {
    ensures to_integer(hi - 1) == to_integer(hi - 1) by { simp(); }
}
```

```expect
fail: its subterm `hi - 1` denotes a value only where 1 condition of that evaluation holds, and the premises in scope where it is stated establish 0 of them, not this one.
  not established: `hi - 1` must not overflow
  premises consulted: none — the premise set this lowering was given is empty, so a premise stated or proved elsewhere in this proof did not reach here
  to repair: state its definedness as a premise in this scope: `defined(hi - 1)`.
```
