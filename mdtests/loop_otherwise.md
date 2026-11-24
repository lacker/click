# Prove facts on the false-guard exit of a loop

The false guard and loop invariant give the proof a lower and upper bound.
The `otherwise` block proves equality from those bounds, and the exact
equality is available to `close()` after the loop. The same proof covers an
initially false guard. A post-tested loop checks the block in the state
reached after executing its body. A short-circuit guard may be false on either
operand.

```c filename=loop_otherwise.c
void count_down(int n) {
    while (n > 0)
        n--;
}

void post_test(int n) {
    do {
        n = 0;
    } while (n > 0);
}

void short_circuit(int n, int m) {
    while (n > 0 && m > 0)
        n = 0;
}
```

```click
verifying "loop_otherwise.c";

void count_down(int32 n) {
    requires n >= 0;
    ensures true;
} by {
    loop {
        invariant n >= 0;
        decreases n;
        otherwise {
            have n == 0 by close();
        }
    }
    have n == 0 by close();
}

void post_test(int32 n) {
    ensures true;
} by {
    loop {
        decreases 0;
        otherwise {
            have n == 0 by close();
        }
    }
    have n == 0 by close();
}

void short_circuit(int32 n, int32 m) {
    requires n >= 0;
    ensures true;
} by {
    loop {
        invariant n >= 0;
        decreases n;
        otherwise {
            have n <= 0 or m <= 0 by close();
        }
    }
}
```

```expect
pass
```
