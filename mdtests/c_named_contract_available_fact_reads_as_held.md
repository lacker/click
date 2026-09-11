# An available named-contract fact prints as held

A `requires SetsZero(callback)` clause puts a named-contract fact on the
callback pointer into the proof context. When a later diagnostic lists what
the proof has, that fact has to read as something the proof holds. The
`branch ensuring` failure below is only a way to print the list: the fact
about `callback` is available, and the missing one is the arithmetic fact
about `y`.

```c filename=named_contract_available_fact.c
int32 pick(void (*callback)(int32*), int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    return y;
}
```

```click
verifying "named_contract_available_fact.c";

contract void SetsZero(int32* cell) {
    owns cell[0..1];
    ensures cell[0] == 0;
}

int32 pick(void (*callback)(int32*), int32 x) {
    requires SetsZero(callback);
    ensures result == result by {
        step();
        branch {
            ensuring {
                fact y == x;
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        step();
        simp();
    }
}
```

```expect
fail: available pure facts: [named contract `SetsZero` holds for callback,
```
