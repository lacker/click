# A refuted match arm's bridge is checked and expands

A `match` arm that bridges facts with `have`s and then refutes itself by
`contradiction` is planned like a sole `contradiction`: its bridge runs in
the arm, and the contradiction excludes the constructor. The bridge is an
ordinary checked step, so `click expand` can select the `solve` inside it.
The other shape, the same arm at function exit, is
[`a_refuted_match_arm_bridge_at_function_exit_is_checked.md`](a_refuted_match_arm_bridge_at_function_exit_is_checked.md).
The original is the post-loop `match c.model ensuring` in
[`rb_ascending_walk_to_root.md`](rb_ascending_walk_to_root.md).

```c filename=a_refuted_match_arm_bridge_is_checked_and_expands.c
int id(int x) { return x; }
```

```click
verifying "a_refuted_match_arm_bridge_is_checked_and_expands.c";

spec enum Tag { A, B }
resource tag() { field model: Tag; }

int id(int x) {
    owns r: tag();
    requires r.model != Tag::A;
    ensures result == x;
    ensures r.model == old(r.model);
} by {
    match r.model {
        Tag::A => { have x == x by close(); contradiction(r.model == Tag::A); },
        Tag::B => { step_until(function.exit); close(); },
    }
}
```

```expect
pass
```
