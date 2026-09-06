# Named contracts authorize abstract function-pointer calls

A named contract describes callable behavior independently of any concrete C
function. A function-pointer parameter carrying that contract can be called
modularly, and a concrete function address satisfies it when the concrete
function has the same verified contract.

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
int32 caller() {
    int32 result;
    result = apply(&compare, 40, 2);
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
