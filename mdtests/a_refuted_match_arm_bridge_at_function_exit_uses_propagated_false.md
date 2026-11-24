# A refuted match arm checks its bridge with propagated false

The arm's constructor contradicts the requirement, so exact propagation
provides `false`. Its bridge `have` has an ordinary proof from that fact;
expansion must retain the checked scope rather than defer or skip it.
The reachable-arm control is
[`a_reachable_match_arm_bridge_at_function_exit_rejects_a_false_have.md`](a_reachable_match_arm_bridge_at_function_exit_rejects_a_false_have.md).

```c filename=a_refuted_match_arm_bridge_at_function_exit_rejects_a_false_have.c
int id(int x) { return x; }
```

```click
verifying "a_refuted_match_arm_bridge_at_function_exit_rejects_a_false_have.c";

spec enum Tag { A, B }
resource tag() { field model: Tag; }

int id(int x) {
    owns r: tag();
    requires r.model != Tag::A;
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
pass
```
