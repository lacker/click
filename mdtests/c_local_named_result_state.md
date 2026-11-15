# A C local named `result` is read through a statement state

After function exit the local `result` is out of scope; the postcondition
names it as `c(result)` at a recorded program point, distinct from the
contract `result`.

```c filename=local_named_result.c
int32 local_named_result(int32 x) {
    int32 result;
    result = x;
    return result;
}
```

```click
verifying "local_named_result.c";

int32 local_named_result(int32 x) {
    ensures result == at(region(2).entry, c(result));
}
```

```expect
pass
```
