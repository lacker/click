# A C name spelled `true` keeps its C meaning

C's `true` and `false` are conveniences, not reserved words, so a C program
may name a parameter `true`. Inside that function's contract the C name
wins: `true` here is the `int` parameter, not the `bool` literal.

```c filename=named_true.c
int shifted(int true) { return true + 1; }
```

```click
verifying "named_true.c";

int32 shifted(int32 true) {
    requires true > 3 and true < 100;
    ensures result == true + 1;
    ensures result > 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
