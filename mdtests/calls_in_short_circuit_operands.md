# Calls in short-circuit operands remain lazy

The call in the unselected operand must not execute. The callee's impossible
precondition makes hoisting it out of the logical expression unsound.

```c filename=short_circuit_calls.c
int32 unavailable_call(void) {
    return 0;
}

int32 counter = 0;

int32 increment_counter(void) {
    counter = counter + 1;
    return 1;
}

int32 skip_and(int32 condition) {
    return condition && unavailable_call();
}

int32 skip_or(int32 condition) {
    return condition || unavailable_call();
}

int32 skip_in_loop(int32 condition) {
    while (condition && unavailable_call()) {
        return 1;
    }
    return 0;
}

int32 selected_and(int32 condition) {
    return condition && increment_counter();
}

int32 selected_or(int32 condition) {
    return condition || increment_counter();
}
```

```click
verifying "short_circuit_calls.c";

int32 unavailable_call() {
    requires 0 == 1;
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 increment_counter() {
    requires counter < 100;
    owns &counter[0..1];
    ensures result == 1;
    ensures counter == old(counter) + 1;
} by {
    execute();
    simp();
}

int32 skip_and(int32 condition) {
    requires condition == 0;
    owns &counter[0..1];
    ensures result == 0;
    ensures counter == old(counter);
} by {
    execute();
    simp();
}

int32 skip_or(int32 condition) {
    requires condition != 0;
    owns &counter[0..1];
    ensures result == 1;
    ensures counter == old(counter);
} by {
    execute();
    simp();
}

int32 skip_in_loop(int32 condition) {
    requires condition == 0;
    owns &counter[0..1];
    ensures result == 0;
    ensures counter == old(counter);
} by {
    execute();
    simp();
}

int32 selected_and(int32 condition) {
    requires condition != 0 and counter < 100;
    owns &counter[0..1];
    ensures result == 1;
    ensures counter == old(counter) + 1;
} by {
    execute();
    simp();
}

int32 selected_or(int32 condition) {
    requires condition == 0 and counter < 100;
    owns &counter[0..1];
    ensures result == 1;
    ensures counter == old(counter) + 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
