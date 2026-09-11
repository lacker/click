# A concrete `executes` clause must restate the C signature

The call the theorem runs is an ordinary C call, so the written parameter list
has to be the callee's own. Here `increment` takes an `int32` by value while
the clause and the target contract write `int32*`, and the mismatch is reported
against the C signature rather than left to the call.

```c filename=c_contract_executes_concrete_rejects_signature.c
void increment(int32 state) { }
```

```click
verifying "c_contract_executes_concrete_rejects_signature.c";

spec enum Mark { Clear, Set }
resource Counter() { field model: Mark; field revision: int32; }

contract Exact(cell: Counter()) for void(int32* state) {
    owns cell;
    ensures cell.model == Mark::Set;
}

void increment(int32 state) {
    owns first: Counter();
    ensures first.model == Mark::Set;
} by {
    unfold(first);
    execute();
    let first = fold(Counter(), { model: Mark::Set, revision: 1 });
    simp();
}

theorem increment_is_exact() executes increment(int32* state) {
    ensures Exact(&increment) as { cell: c } by {
        step(increment(state), { first: c });
        simp();
    }
}
```

```expect
fail: the executes parameter list does not match the C signature of `increment`
```
