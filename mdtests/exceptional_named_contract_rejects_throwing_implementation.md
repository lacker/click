# A throwing function does not meet a contract that does not throw

`Fallible` here never throws, so a caller of `apply` may rely on a normal
return; `helper` may throw, so it cannot be passed for it.

```c filename=exceptional_named_contract_rejects_throwing_implementation.c
int32 apply(int32 (*f)(int32), int32 x) {
    return f(x);
}

int32 helper(int32 x) {
    return x;
}

int32 steady(int32 x) {
    return x;
}

int32 caller(int32 x) {
    return apply(helper, x);
}

int32 calm(int32 x) {
    return apply(steady, x);
}
```

```click
verifying "exceptional_named_contract_rejects_throwing_implementation.c";

contract int32 Fallible(int32 x) {
    ensures result == x;
}

int32 apply(int32 (*f)(int32), int32 x) {
    requires Fallible(f);
    ensures result == x;
}

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 steady(int32 x) {
    ensures result == x;
}

theorem proposed_helper_is_fallible() {
    ensures Fallible(&helper) by { unfold(Fallible(&helper)); close(); }
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 calm(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

```expect
fail: `helper` is not a verified or external function compatible with contract `Fallible`
```
