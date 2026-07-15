# explicit loop initialization and preservation proofs

This checks the two premises of an abstract loop rule. Initialization is a pure
proof at loop entry, while preservation is an execution proof of one arbitrary
iteration. The invariant predicate remains opaque unless the written theorem
applications are used.

```c filename=loop_explicit_initialize_and_preserve.c
int32 loop_explicit_initialize_and_preserve(int32 x) {
    while (x < 1) {
        x = 0;
    }
    return x;
}
```

```click
verifying "loop_explicit_initialize_and_preserve.c";

predicate acceptable(int32 x) {
    x >= 0
}

theorem nonnegative_is_acceptable(x: int32) {
    requires x >= 0;

    ensures acceptable(x) by {
        unfold(acceptable);
        simp();
    }
}

int32 loop_explicit_initialize_and_preserve(int32 x) {
    requires x >= 0;

    for loop(0) {
        invariant acceptable(x);

        initialize by {
            apply(nonnegative_is_acceptable(x));
            simp();
        }

        preserve by {
            execute_step();
            apply(nonnegative_is_acceptable(x));
            simp();
        }
    }

    ensures acceptable(result) by {
        execute_rest();
        unfold(acceptable);
        simp();
    }
}
```

```expect
pass
```
