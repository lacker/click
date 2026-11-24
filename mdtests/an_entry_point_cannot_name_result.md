# An entry program point cannot name `result`

A program point before the return cannot name `result`. A proof that states
`at(function.entry, result == 5)` is refused with the program point it named.

```c filename=entry_result.c
int h(int x) { x = 5; return x; }
```

```click
verifying "entry_result.c";

int h(int x) {
    ensures result == 5;
} by {
    step_until(function.exit);
    have at(function.entry, result == 5) by { close(); }
    close();
}
```

```expect
fail: `result` cannot be named inside `at(function.entry, ...)`
```
