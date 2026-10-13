# a step's `requires` entry may prove each obligation once

Two entries that state the same obligation are refused at the second, which
names the entry it repeats.

```c filename=step_requires_repeated_entry.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "step_requires_repeated_entry.c";

int32 first(int32 x, int32 y) {
    requires x > 0 or y > 0;
    requires y > 0 or x > 0;
    ensures 1 == 1 by auto;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        step() {
            requires a > 0 or b > 0 by simp;
            requires a > 0 or b > 0 by simp;
        }
        step();
        simp();
    }
}
```

```expect
fail: proves the same obligation as `requires` entry 1
```
