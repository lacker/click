# A `do ... while` with no `break` states its exit too

`do { i++; } while (0);` leaves the loop the only way it can, through the guard
it reads after the body. With that exit unrecorded, the loop had no exit state
at all and any postcondition followed, including this one, which is false for
every input. The exit is now the body's end state, where `i` is the head's
abstract value incremented once, and `result == 99` is refused there.

The provable claim on the same C is
[`c_do_while.md`](c_do_while.md)'s `do_while_invariant`.

```c filename=do_while_any.c
int32 do_while_any(int32 i) {
    do {
        i++;
    } while (0);
    return i;
}
```

```click
verifying "do_while_any.c";

int32 do_while_any(int32 i) {
    requires i == 0;
    ensures result == 99;
} by {
    loop {
        invariant i >= 0 and i < 2147483647;
    }
    step();
    simp();
}
```

```expect
fail: unclosed goal: result == 99
```
