# an unavailable theorem requirement names itself and its instantiation

`required exact fact ... : int32 equality is true` named a shape, not a fact. A
reader fixes this refusal by supplying the missing premise, so the sentence has
to say which requirement is missing, what its parameters were bound to, and the
fact the application instantiated it to, with both sides.

Here the first requirement holds of the entry array and the second does not, so
the report has to distinguish them, and `a = old(box)` is what makes the
instantiated cell the entry one.

```c filename=apply_theorem_requirement_names_its_instantiation.c
int32 raise_head(int32 box[1]) {
    box[0] = 9;
    return 0;
}
```

```click
verifying "apply_theorem_requirement_names_its_instantiation.c";

theorem head_below_one_is_below_two(a: int32[], seed: int32) {
    requires a[0] == seed;
    requires a[0] < 1;

    ensures a[0] < 2 by {
        close();
    }
}

int32 raise_head(int32 box[1]) {
    requires box[0] == 7;
    owns box[0..1];
    ensures unreported_requirement: old(box[0]) < 2 by {
        step_until(function.exit);
        apply(head_below_one_is_below_two(old(box), 7));
        close();
    }
}
```

```expect
fail: has an unproved obligation: `old(box)[0] < 1`
```
