# A bare function designator forms the same address as `&name`

C decays a function designator used as a value to a pointer to that function,
which is how callbacks are usually passed: `apply(compare, 40, 2)`. The
argument denotes the same address as `&compare`, so it satisfies the named
contract the callee requires by exactly the same concrete formation.

```c filename=compare.c
int32 compare(int32 left, int32 right) {
    return left - right;
}
```

```c filename=apply.c
int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    int32 result;
    result = callback(left, right);
    return result;
}
```

```c filename=caller.c
int32 compare(int32 left, int32 right);
int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right);

int32 caller() {
    int32 result;
    result = apply(compare, 40, 2);
    return result;
}
```

```click
verifying "compare.c";
verifying "apply.c";
verifying "caller.c";

contract int32 Comparator(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right;
}

int32 compare(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right by auto;
}

int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    requires Comparator(callback);
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right by auto;
}

int32 caller() {
    ensures result == 38 by auto;
}
```

```expect
pass
```
