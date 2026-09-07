# Callback refinement frames a symbolic resource quantity

A callback that preserves only the `used` credits can satisfy an interface
that preserves all `available` credits when the target precondition proves
`used <= available`. Refinement splits the symbolic quantity, frames the
unused remainder, and recombines it after the callback. The same rule works
both when forming a contract for a concrete function and when proving one
named callback contract from another.

```c filename=quantified_callback_refinement.c
void keep_used(int32 available, int32 used) {
}

void invoke_preserving(
    void (*callback)(int32, int32),
    int32 available,
    int32 used
) {
    callback(available, used);
}

void concrete_quantity_caller(int32 available, int32 used) {
    invoke_preserving(&keep_used, available, used);
}

void abstract_quantity_caller(
    void (*callback)(int32, int32),
    int32 available,
    int32 used
) {
    invoke_preserving(callback, available, used);
}
```

```click
abstract resource credit();

verifying "quantified_callback_refinement.c";

contract void PreserveUsed(int32 available, int32 used) {
    requires 0 <= used;
    owns used of credit();
}

contract void PreserveAvailable(int32 available, int32 used) {
    requires 0 <= used and used <= available;
    owns available of credit();
}

theorem preserving_used_preserves_available(
    callback: void (*)(int32, int32)
) {
    requires PreserveUsed(callback);
    ensures PreserveAvailable(callback) by {
        unfold(PreserveUsed);
        unfold(PreserveAvailable);
        simp();
    }
}

void keep_used(int32 available, int32 used) {
    requires 0 <= used;
    owns used of credit();
} by auto;

void invoke_preserving(
    void (*callback)(int32, int32),
    int32 available,
    int32 used
) {
    requires PreserveAvailable(callback);
    requires 0 <= used and used <= available;
    owns available of credit();
} by auto;

void concrete_quantity_caller(int32 available, int32 used) {
    requires 0 <= used and used <= available;
    owns available of credit();
} by auto;

void abstract_quantity_caller(
    void (*callback)(int32, int32),
    int32 available,
    int32 used
) {
    requires PreserveUsed(callback);
    requires 0 <= used and used <= available;
    owns available of credit();
} by {
    apply(preserving_used_preserves_available(callback));
    execute();
    simp();
}
```

```expect
pass
```
