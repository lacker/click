# A loop condition's call and test refuse a false count

The loop of
[`a_loop_condition_s_call_and_test_are_the_loop_s_own.md`](a_loop_condition_s_call_and_test_are_the_loop_s_own.md)
with a postcondition one more than what it returns. The same proof reaches the
return with `c == n` and refuses the claim.

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
    ensures to_integer(result) == to_integer(n) + 1;
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
            }
        }
    }
    have at(statement(2).call(take, 0).entry, left) == 0 by {
        if at(statement(2).call(take, 0).entry, left) == 0 {
            close();
        } else {
            have statement(2).call(take, 0).result == 1 by close();
            have statement(2).call(take, 0).result != 1 by close();
            contradiction(statement(2).call(take, 0).result == 1);
        }
    }
    have at(loop(0).test().entry, left) == 0 by close();
}
```

```expect
fail: failed for `count.ensures_0`
```
