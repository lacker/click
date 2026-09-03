# Direct introductions after execution

The checked outcome driver should allow a quantified postcondition to be
introduced directly after execution reaches function exit. A nested `have`
should not be required solely to place the quantified binder in scope.

```c filename=post_execution_intro_quantified_ensure.c
int32 forall_scope(int32 value) {
    return value;
}
```

```click
verifying "post_execution_intro_quantified_ensure.c";

int32 forall_scope(int32 value) {
    ensures forall (k: int32) {
        (k == k and value == value) implies k == k
    } by {
        execute();
        intro();
        intro();
        simp();
    }
}
```

```expect
pass
```
