# a `diverges` marker needs something that may not return

`diverges` is required on, and only on, a function that may not return. This
function's only loop is ranked and it calls nothing, so it has termination
evidence in everything but name, and the marker would hide that from every
caller. The refusal is local: it reads this function's loops and calls and no
other function's body.

```c filename=diverges_rejects_unjustified_marker.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "diverges_rejects_unjustified_marker.c";

int32 drain(int32 n) diverges {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
        initialize by close();
        maintain by {
            have 0 <= to_integer(n - 1);
            step();
        }
    }
    step();
    close();
}
```

```expect
fail: `drain` is declared `diverges`, but every loop it runs is ranked and every call it makes descends; remove the marker
```
