# A constant-looking C parameter cannot prove a false contract

Replacing the parameter reference with floating infinity would prove this
incorrect contract. The unchanged C function returns zero for nonpositive
inputs, so verification must fail.

```c filename=positive.c
int positive(int INFINITY) { return INFINITY > 0; }
```

```click
verifying "positive.c";
int positive(int INFINITY) {
    ensures result == 1;
}
```

```expect
fail: positive.ensures_0
```
