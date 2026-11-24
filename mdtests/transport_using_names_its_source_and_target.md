# An unproved equality keeps its parameter names

The premise `a == 1` cannot prove the unrelated goal `b == 1`. Ordinary
fact checking refuses the goal and prints both the available premise and
the unproved goal with their distinct parameter names.

```c filename=transport_using_names_its_source_and_target.c
void unused(void) {}
```

```click
verifying "transport_using_names_its_source_and_target.c";

theorem t(a: int32, b: int32) {
    requires a == 1;
    ensures b == 1 by {
        close();
    }
}
```

```expect
fail: could not establish `b == 1`
```
