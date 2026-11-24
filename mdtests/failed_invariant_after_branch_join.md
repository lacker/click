# A failed invariant after a branch join names the join

The then arm violates the invariant; the else arm preserves it. Both steps
succeed, and the implicit back-edge obligation fails in their joined state.

```c filename=loop.c
unsigned long branch_drain(unsigned long len, int flag) { while (len >= 16) { if (flag == 0) { len -= 16; } else { len = 16; } } return len; }
```

```click
target "x86_64-unknown-linux-gnu";
verifying "loop.c";
uint64 branch_drain(uint64 len, int32 flag) {
    requires len == 16u64;
    ensures result <= 16u64;
} by {
    loop {
        invariant len == 16u64;
        initialize by close();
        maintain by {
            branch { true => { step(); } false => { step(); } }
        }
    }
    step_until(function.exit); close();
}
```

```expect
fail: proof step tactic 2: closure body did not prove every invariant obligation
```
