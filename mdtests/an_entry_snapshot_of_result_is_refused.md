# An entry snapshot of `result` is refused

A snapshot taken before the return cannot name `result`. A proof that states
`at(function.entry, result == 5)` is refused with the snapshot it named.

```c filename=entry_result.c
int h(int x) { x = 5; return x; }
```

```click
verifying "entry_result.c";

int h(int x) {
    ensures result == 5;
} by {
    execute();
    have at(function.entry, result == 5) by { simp(); }
    assumption();
}
```

```expect
fail: `result` cannot be named inside `at(function.entry, ...)`
```
