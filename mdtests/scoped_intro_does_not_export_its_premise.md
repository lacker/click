# An introduced premise is local to its block

```c filename=scoped_intro_premise.c
int scoped_premise(int x) { return x; }
```

```click
verifying "scoped_intro_premise.c";

int32 scoped_premise(int32 x) {
    ensures x == 0 implies result == 0;
    ensures x == 0;
} by {
    step_until(function.exit);
    intro() {
        rewrite(x, 0);
        close();
    }
    close();
}
```

```expect
fail: x == 0
```
