# A reachable match arm rejects a false bridge have

Without the refuting requirement, the A arm is reachable and its false
bridge claim cannot be proved. This controls the refuted-arm propagation case.

```c filename=a_refuted_match_arm_bridge_at_function_exit_rejects_a_false_have.c
int id(int x) { return x; }
```

```click
verifying "a_refuted_match_arm_bridge_at_function_exit_rejects_a_false_have.c";

spec enum Tag { A, B }
resource tag() { field model: Tag; }

int id(int x) {
    owns r: tag();
    ensures result == x;
    ensures r.model == old(r.model);
} by {
    step_until(function.exit);
    match r.model ensuring { fact result == x; } {
        Tag::A => { have x == x + 1 by close(); contradiction(r.model == Tag::A); },
        Tag::B => { },
    }
    close();
}
```

```expect
fail: `solve` failed
```
