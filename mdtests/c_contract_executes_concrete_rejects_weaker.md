# A concrete execution theorem cannot promise more than the function does

`increment` sets the model but says nothing about the revision, so the single
call leaves the target's second guarantee open. The theorem is refused; being
concrete does not let the conclusion assume its own target.

```c filename=c_contract_executes_concrete_rejects_weaker.c
void increment(int32* state) { }

int32 accept(void (*callback)(int32*)) { return 0; }

int32 caller() { return accept(&increment); }
```

```click
verifying "c_contract_executes_concrete_rejects_weaker.c";

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

int32 accept(void (*callback)(int32*)) {
    requires Exact(callback);
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    apply(increment_is_exact());
    execute();
    simp();
}
```

```expect
fail: unclosed goal: c.revision == 1
```
