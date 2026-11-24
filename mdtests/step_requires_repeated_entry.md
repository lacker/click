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

function is_positive(value: int32) -> int32 { if value > 0 { 1 } else { 0 } }

int32 first(int32 x, int32 y) {
    requires is_positive(x) == 1 or is_positive(y) == 1;
    requires is_positive(y) == 1 or is_positive(x) == 1;
    ensures 1 == 1;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        step() {
            requires is_positive(a) == 1 or is_positive(b) == 1 by {
                have is_positive(a) == 1 by {
                    unfold(is_positive(a)); normalize() using { a > 0; };
                }
                close();
            }
            requires is_positive(a) == 1 or is_positive(b) == 1 by {
                have is_positive(a) == 1 by {
                    unfold(is_positive(a)); normalize() using { a > 0; };
                }
                close();
            }
        }
        step();
        close();
    }
}
```

```expect
fail: proves the same obligation as `requires` entry 1
```
