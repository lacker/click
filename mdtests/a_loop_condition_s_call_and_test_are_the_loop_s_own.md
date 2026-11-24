# A loop condition's call and test are the loop's own regions

`while (take(&left))` calls `take` and tests its result on every pass. The
call and the test are the loop's own atomic regions, between its head and its
body: the pass steps the call, then the test, whose false side leaves the loop
there. No statement of the source is invented for them.

The proof uses `statement(2).call(take, 0).entry` and `.result` to
establish that the call found `left` empty on the false path. That path
exports the count relation before leaving the loop. The post-loop proof
still refers to `loop(0).test().entry` to check the final test's state.
The `otherwise` proof also names the call entry of the pass that left.

```c filename=take_loop.c
int take(int *n) {
    if (*n == 0) return 0;
    *n = *n - 1;
    return 1;
}
unsigned count(int n) {
    int left = n;
    unsigned c = 0;
    while (take(&left)) {
        c = c + 1;
    }
    return c;
}
```

```click
verifying "take_loop.c";
int take(int *n) {
    requires *n >= 0;
    owns n[0..1];
    ensures result == (if old(*n) == 0 { 0 } else { 1 });
    ensures *n == (if old(*n) == 0 { 0 } else { old(*n) - 1 });
}
unsigned count(int n) {
    requires n >= 0;
    ensures to_integer(result) == to_integer(n);
} by {
    step_until(loop(0).entry);
    loop {
        decreases to_integer(n) - to_integer(c);
        invariant left >= 0;
        invariant to_integer(c) + to_integer(left) == to_integer(n);
        maintain by {
            step();
            have statement(2).call(take, 0).result
                == (if at(statement(2).call(take, 0).entry, left) == 0 { 0 } else { 1 }) by close();
            have left
                == (if at(statement(2).call(take, 0).entry, left) == 0 { 0 }
                    else { at(statement(2).call(take, 0).entry, left) - 1 }) by close();
            if statement(2).call(take, 0).result != 0 {
                have at(statement(2).call(take, 0).entry, left) != 0 by {
                    if at(statement(2).call(take, 0).entry, left) == 0 {
                        have statement(2).call(take, 0).result == 0 by close();
                        contradiction(statement(2).call(take, 0).result == 0);
                    } else {
                        close();
                    }
                }
                have left == at(statement(2).call(take, 0).entry, left) - 1 by close();
            } else {
                have at(statement(2).call(take, 0).entry, left) == 0 by {
                    if at(statement(2).call(take, 0).entry, left) == 0 {
                        close();
                    } else {
                        have statement(2).call(take, 0).result == 1 by close();
                        have statement(2).call(take, 0).result != 1 by close();
                        contradiction(statement(2).call(take, 0).result == 1);
                    }
                }
                have left == 0 by close();
                have to_integer(c) + to_integer(at(statement(2).call(take, 0).entry, left))
                    == to_integer(n) by close();
                have to_integer(c) == to_integer(n) by close();
            }
        }
        otherwise {
            have at(statement(2).call(take, 0).entry, left) == 0 by close();
        }
    }
    have at(loop(0).test().entry, left) == 0 by close();
}
```

```expect
pass
```
