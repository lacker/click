# Marking the current proof frontier

`mark name;` records the current execution state under a proof-local name.
Later `at(name, ...)` expressions read that state without depending on a
numbered C statement coordinate. A mark does not move execution.

```c filename=proof_mark_current_frontier.c
int32 set_twice(int32 x) {
    x = 1;
    x = 2;
    return x;
}
```

```click
verifying "proof_mark_current_frontier.c";

int32 set_twice(int32 x) {
    ensures result == at(after_first_write, x) + 1 by {
        step();
        mark after_first_write;
        execute();
        simp();
    }
}
```

```expect
pass
```
