# Expression calls cannot be reordered across potentially aliased reads

The unchanged C reproduction previously verified the false `result == 2`
contract by hoisting `set(&x)` ahead of the left operand's read of `x`.
Because C permits the opposite evaluation order, Click rejects the unsupported
call/read interaction at the call site.

```c filename=call_read_order.c
static inline int set(int *p) { *p = 2; return 0; }
int order(void) { int x = 1; return x + set(&x); }
```

```click
verifying "call_read_order.c";

int32 order() {
    ensures result == 2;
}
```

```expect
fail: an expression call and a potentially aliased operand read are not supported
```
