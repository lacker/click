# Pointer casts retain their current-expression requirement

Integer value casts do not change the source validation for pointer casts.
The state belongs around the pointer cast.

```c filename=historical_pointer.c
int *identity(int *p) { return p; }
```

```click
verifying "historical_pointer.c";
int32* identity(int32* p) {
    ensures result == (old(p) as (int32 *));
}
```

```expect
fail: scalar cast expects a current expression
```
