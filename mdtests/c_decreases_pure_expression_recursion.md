# a C recursion measure may be a pure expression

The measure is not a parameter: it is an application of a pure Click function,
which `decreases <int32 parameter>` cannot name. The kernel reads that one
declared expression at `drain`'s own entry, giving the value the recursion
starts from, and again at each call to `drain` inside it, and asks the proof
for the two members a ranked loop's back edge owes: the callee's measure is
nonnegative, and it is strictly below the entry value.

Nothing analyses the body. The descent is an ordinary verification condition
at the recursive `step()`, so the proof states it, exactly as it states a
precondition the call site owes. The application is opaque, so each `have`
unfolds it; that is the whole difference from `decreases n`.

```c filename=c_decreases_pure_expression_recursion.c
int32 drain(int32 n) {
    int32 result;
    if (n > 0) {
        result = drain(n - 1);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_pure_expression_recursion.c";

function level(n: int32) -> int32 {
    n
}

int32 drain(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    branch {
        then {
            have 0 <= level(n - 1) by {
                unfold(level(n - 1));
                apply(int32_positive_predecessor_is_nonnegative(n)) using {
                    n > 0;
                }
            }
            have level(n - 1) < level(n) by {
                unfold(level(n - 1));
                unfold(level(n));
                apply(int32_positive_predecessor_strictly_decreases(n)) using {
                    n > 0;
                }
            }
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    simp();
}
```

```expect
pass
```
