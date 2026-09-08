# Startup cannot assume extra ownership or arbitrary facts

```c filename=main.c
int state = 7;
int main(void) { return state; }
```

```click
verifying "main.c";
int main() {
    consumes &state[0..1];
    ensures result == 7;
} by { execute(); simp(); }
```

```expect
fail: program-entry main currently requires no parameters or preconditions
```
