# A concrete function satisfies a proof-parameter contract by execution

`executes` names a verified C function instead of a callback parameter, so the
theorem has no callback parameter and no source-contract premise: the source is
`increment`'s own verified contract, run by the single call step. The
conclusion's `as` map introduces the target's arbitrary instance, and
`apply(increment_is_exact())` introduces `Exact(&increment)` at the call site
exactly like a concrete `unfold` refinement theorem.

```c filename=c_contract_executes_concrete.c
void increment(int32* state) { }
void invoke(void (*callback)(int32*), int32* state) { callback(state); }
void concrete_caller(int32* state) { invoke(&increment, state); }
```

```click
verifying "c_contract_executes_concrete.c";

spec enum Mark { Clear, Set }
resource Counter() { field model: Mark; field revision: int32; }

contract Exact(cell: Counter()) for void(int32* state) {
    owns cell;
    ensures cell.model == Mark::Set;
    ensures cell.revision == 1;
}

void increment(int32* state) {
    owns first: Counter();
    ensures first.model == Mark::Set;
    ensures first.revision == 1;
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

void invoke(void (*callback)(int32*), int32* state) {
    requires Exact(callback);
    owns k: Counter();
    ensures k.model == Mark::Set;
    ensures k.revision == 1;
} by {
    step(Exact(k));
    execute();
    simp();
}

void concrete_caller(int32* state) {
    owns mine: Counter();
    ensures mine.model == Mark::Set;
    ensures mine.revision == 1;
} by {
    apply(increment_is_exact());
    step(invoke(&increment, state), { k: mine });
    execute();
    simp();
}
```

```expect
pass
```
