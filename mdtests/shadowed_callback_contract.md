# a shadowing callback parameter answers from its own contract

The companion to `termination_shadowed_callback_rejected.md`. The file-scope
`helper` returns 2 and the callback contract `One` promises 1; `f` proves
`result == 1`, so the call goes through the parameter that hides the function,
not through the function.

```c filename=shadowed_callback_contract.c
int32 helper(int32 x) {
    return 2;
}

int32 f(int32 (*helper)(int32)) {
    return helper(1);
}
```

```click
verifying "shadowed_callback_contract.c";

contract int32 One(int32 x) {
    ensures result == 1;
}

int32 helper(int32 x) {
    ensures result == 2;
}

int32 f(int32 (*helper)(int32)) {
    requires One(helper);
    ensures result == 1;
}
```

```expect
pass
```
