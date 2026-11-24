# A failing `have` reports its written operation

The checked driver runs this source body once. Its first `close()` cannot prove
`n + 1 > 500`, so that operation reports the failure before the following
`normalize()` runs. The diagnostic retains the source body position and the
failing goal. A whole-script shape precheck must not hide this failure, and no
generated-script driver may retry the source.

```c filename=have_body_declines_names_the_goal.c
int spin(int n) {
    return n;
}
```

```click
verifying "have_body_declines_names_the_goal.c";

int spin(int n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    have n + 1 > 500 by {
        close();
        normalize();
    }
}
```

```expect
fail: have body tactic 1: `solve` failed for `spin.contract`: could not establish `(to_integer(n) + 1) > 500`
```
