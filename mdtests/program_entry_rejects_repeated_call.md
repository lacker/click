# Calling main is not another program startup

```c filename=main.c
int state = 7;
int main(void) { state += 1; return state; }
int again(void) { main(); return main(); }
```

```click
verifying "main.c";
int main() { ensures result == 8; } by { execute(); simp(); }
int again() {
    owns &state[0..1];
    ensures result == 8;
} by { execute(); simp(); }
```

```expect
fail: again.contract
```
