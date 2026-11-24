# Live and exit-time call payloads

A returned binding names the callee's result before the caller transforms it.
A thrown binding names the callee's exception. Both names are local to their
arm.

```c filename=outcomes_payload_bindings.c
int32 helper(int32 x) { return x; }
int32 live(void) { return helper(5) + 1; }
int32 deferred(void) { return helper(5) + 1; }
```

```click
verifying "outcomes_payload_bindings.c";

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 live() throws int32 {
    ensures result == 6;
    exceptional ensures exception == 7;
} by {
    outcomes {
        returned(value) => {
            step();
            have value == 5 by close();
            close();
        }
        threw(error) => {
            have error == 7 by close();
            close();
        }
    }
}

int32 deferred() throws int32 {
    ensures result == 6;
    exceptional ensures exception == 7;
} by {
    step();
    outcomes {
        returned(value) => {
            have value == 5 by close();
            close();
        }
        threw(error) => {
            have error == 7 by close();
            close();
        }
    }
}
```

```expect
pass
```
