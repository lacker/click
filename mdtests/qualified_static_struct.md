# Qualified ownership of private struct fields

```c filename=counter.c
struct counter { unsigned long value; };
static struct counter state = {7};
unsigned long read_value(struct counter *p) { return p->value; }
unsigned long current(void) { return read_value(&state); }
```

```c filename=main.c
unsigned long current(void);
int main(void) { return current() == 7; }
```

```click
verifying "counter.c" as counter;
verifying "main.c";

resource counter_state() {
    owns counter::state.value;
    fact counter::state.value == 7u64;
}

unsigned long read_value(struct counter *p) {
    owns p->value;
    ensures result == old(p->value);
    ensures p->value == old(p->value);
}

unsigned long current() {
    owns counter_state();
    ensures result == old(counter::state.value);
    ensures result == 7u64;
} by {
    unfold(counter_state());
    have old(counter::state.value) == 7u64;
    step_until(function.exit);
    fold(counter_state());
    known();
    known();
    rewrite(result, old(counter::state.value));
    solve();
}

int main() {
    ensures result == 1;
} by {
    have counter::state.value == 7u64;
    fold(counter_state());
}
```

```expect
pass
```
