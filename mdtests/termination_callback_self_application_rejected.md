# a function cannot be its own callback

`apply` returns whenever its callback does, and `spin` hands it `spin`. Each
function's contract holds if it returns, and neither ever does. No direct call
closes the cycle: `apply` reaches `spin` only through the pointer, so the
direct-call graph shows a caller above a callee and nothing more.

The rule that refuses it is about the address. A function reached through a
function pointer must return without calling through one, in its own body or
below, because only then can no pointer call re-enter its caller. `spin` calls
`apply`, which calls through a pointer, so `spin` may not be handed out.

```c filename=termination_callback_self_application_rejected.c
int32 apply(int32 (*callback)(int32), int32 x) {
    int32 result;
    result = callback(x);
    return result;
}

int32 spin(int32 x) {
    int32 result;
    result = apply(spin, x);
    return result;
}
```

```click
verifying "termination_callback_self_application_rejected.c";

contract int32 Unary(int32 x) {
    ensures 0 == 0;
}

int32 apply(int32 (*callback)(int32), int32 x) {
    requires Unary(callback);
    ensures 0 == 0 by auto;
}

int32 spin(int32 x) {
    ensures 0 == 0 by auto;
}
```

```expect
fail: could not certify termination for `spin`: it takes the address of `spin`, and a function reached through a function pointer must return without calling through one
```
