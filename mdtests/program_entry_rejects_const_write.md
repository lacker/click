# Startup never supplies write permission for const storage

```c filename=main.c
const int state = 7;
void overwrite(int *p) { *p = 9; }
int main(void) { overwrite((int *)&state); return state; }
```

```click
verifying "main.c";
void overwrite(int *p) {
    requires loadable(p[0..1]);
    consumes p[0..1];
    produces p[0..1];
    ensures p[0] == 9;
} by { execute(); simp(); }
int main() { ensures result == 9; } by { execute(); simp(); }
```

```expect
fail: cannot discard const qualification
```
