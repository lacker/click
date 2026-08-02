# reach hides unexported preconditions

Even stable parameters retain only their symbolic identity. Pure preconditions
must be exported when the continuation needs them.

```c filename=advance_hidden_requirement.c
int32 advance_hidden_requirement(int32 x) {
    int32 y;
    y = 0;
    return x;
}
```

```click
verifying "advance_hidden_requirement.c";

int32 advance_hidden_requirement(int32 x) {
    requires x >= 0;

    ensures result >= 0 by {
        step();
        reach(statement(1).exit)
        ensuring {
            fact y == 0;
        }
        by {
            step();
        }
        step();
        simp();
    }
}
```

```expect
fail: unclosed goal: result >= 0
```
