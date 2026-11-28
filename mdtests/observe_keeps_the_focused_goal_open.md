# A memory observation leaves the focused goal open

The observation establishes the viewability fact. A later `have` still runs
in the same proof block before `close()` discharges the goal.

```c filename=observe_keeps_the_focused_goal_open.c
void keep(int32* p) {}
```

```click
verifying "observe_keeps_the_focused_goal_open.c";

void keep(int32* p) {
    owns p[0..1];
    ensures viewable(p[0..1]);
} by {
    step_until(function.exit);
    have viewable(p[0..1]) by {
        observe(p[0..1]);
        have p == p by close();
        close();
    }
}
```

```expect
pass
```
