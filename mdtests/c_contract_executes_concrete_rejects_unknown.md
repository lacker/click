# A concrete execution theorem needs a function the project has a rule for

`increment` appears in the C source but carries no sidecar, so the project has
neither a verified nor an explicitly external contract for it. Running it would
prove nothing about it, and the theorem is refused before any proof runs.

```c filename=c_contract_executes_concrete_rejects_unknown.c
void increment(int32* state) { }

int32 accept(void (*callback)(int32*)) { return 0; }

int32 caller() { return accept(&increment); }
```

```click
verifying "c_contract_executes_concrete_rejects_unknown.c";

contract void Quiet(int32* state) {
    ensures state != 0;
}

theorem increment_is_quiet() executes increment(int32* state) {
    ensures Quiet(&increment) by {
        execute();
        simp();
    }
}

int32 accept(void (*callback)(int32*)) {
    requires Quiet(callback);
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    apply(increment_is_quiet());
    execute();
    simp();
}
```

```expect
fail: `increment` is not a verified or external function in this project
```
