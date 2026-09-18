# a `diverges` named contract verifies in a caller that says so

The same call, in a `run` that declares `diverges`. The marker is what the
contract already admitted, so the partial-correctness proof stands and the
marker is justified: the pointer call is the one thing here that may not
return, and nothing asks `run` to remove it.

```c filename=diverges_named_contract_in_marked_caller.c
int32 run(int32 (*step)(int32), int32 x) {
    int32 result;
    result = step(x);
    return result;
}
```

```click
verifying "diverges_named_contract_in_marked_caller.c";

contract int32 Spinner(int32 x) diverges {
    ensures result == 1;
}

int32 run(int32 (*step)(int32), int32 x) diverges {
    requires Spinner(step);
    ensures result == 1 by auto;
}
```

```expect
pass
```
