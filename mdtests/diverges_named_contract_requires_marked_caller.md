# a `diverges` named contract needs the caller to say so too

A named contract is the whole of what a call through a function pointer may
assume. Nothing here names the implementation behind `step`: it arrives from
outside this project, and a `diverges` contract admits one that never returns.
So `run` may not return either, and a `run` with no marker would be certified
to return while an admitted execution of it does not.

```c filename=diverges_named_contract_requires_marked_caller.c
int32 run(int32 (*step)(int32), int32 x) {
    int32 result;
    result = step(x);
    return result;
}
```

```click
verifying "diverges_named_contract_requires_marked_caller.c";

contract int32 Spinner(int32 x) diverges {
    ensures result == 1;
}

int32 run(int32 (*step)(int32), int32 x) {
    requires Spinner(step);
    ensures result == 1 by auto;
}
```

```expect
fail: the named contract `Spinner` is declared `diverges`, so the call through `step` may not return; declare `run` `diverges` too, or require a contract without the marker
```
