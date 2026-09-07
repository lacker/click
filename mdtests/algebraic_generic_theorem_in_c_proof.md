# a C proof applies a checked generic theorem instance

```c filename=algebraic_generic_theorem_in_c_proof.c
int32 passthrough(int32 value) {
    return value;
}
```

```click
verifying "algebraic_generic_theorem_in_c_proof.c";

theorem symmetric<T>(left: T, right: T) {
    requires left == right;
    ensures right == left by {
        rewrite(left == right);
        normalize();
    }
}

int32 passthrough(int32 value) {
    ensures value == result;
} by {
    execute();
    apply(symmetric(result, value));
    simp();
}
```

```expect
pass
```
