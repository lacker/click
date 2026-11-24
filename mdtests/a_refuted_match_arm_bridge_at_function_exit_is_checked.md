# A refuted match arm's bridge at function exit is checked

After `step_until(function.exit)` the proof stands at function exit, where an ordinary arm's
tactics are deferred to each outcome path. A refuted arm has no outcome path,
so its bridge is checked where it is written: a deferred `have` would never
run. A bridge justified by propagated false is checked in
[`a_refuted_match_arm_bridge_at_function_exit_uses_propagated_false.md`](a_refuted_match_arm_bridge_at_function_exit_uses_propagated_false.md).
Without a refuting assumption, the reachable-arm control refuses a false bridge:
[`a_reachable_match_arm_bridge_at_function_exit_rejects_a_false_have.md`](a_reachable_match_arm_bridge_at_function_exit_rejects_a_false_have.md).

```c filename=a_refuted_match_arm_bridge_at_function_exit_is_checked.c
int id(int x) { return x; }
```

```click
verifying "a_refuted_match_arm_bridge_at_function_exit_is_checked.c";

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
        Tag::A => { have x == x by close(); contradiction(r.model == Tag::A); },
        Tag::B => { },
    }
    close();
}
```

```expect
pass
```
