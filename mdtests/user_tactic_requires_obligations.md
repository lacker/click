# User-defined tactic requirements are call-site obligations

The explicit call proves both argument definedness and the instantiated
requirement. The bare call uses the implicit closer. The last call names its
one requirement through the caller's held resource.

```c filename=user_tactic_requires.c
void explicit_proof(int32 n) {}
void implicit_proof(int32 n) {}
void resource_proof(int32 n) {}
```

```click
verifying "user_tactic_requires.c";

resource counter() { field next: int32; }

tactic make_counter(n: int32) {
    requires 1 <= n;
    produces item: counter();
} by {
    let item = fold(counter(), { next: n });
}

tactic discard_counter(n: int32) {
    consumes input: counter();
    requires input.next == n;
} by {
    unfold(input);
}

void explicit_proof(int32 n) {
    requires 0 <= n;
    requires n < 2147483647;
    produces c: counter();
} by {
    let { item: c } = make_counter(n + 1) {
        requires defined(n + 1) by { close(); }
        requires 1 <= ((n + 1) as int32) by { close(); }
    }
}

void implicit_proof(int32 n) {
    requires 0 <= n;
    requires n < 2147483647;
    produces c: counter();
} by {
    let { item: c } = make_counter(n + 1);
}

void resource_proof(int32 n) {
    consumes held: counter();
    requires held.next == n;
} by {
    discard_counter(n, { input: held }) by { close(); }
}
```

```expect
pass
```
