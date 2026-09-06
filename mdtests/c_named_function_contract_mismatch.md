# Concrete callbacks must match the named contract

A compatible C signature is insufficient. The concrete callback below has a
different verified postcondition, so its address cannot satisfy `Difference`.

```c filename=sum.c
int32 sum(int32 left, int32 right) {
    return left + right;
}
```

```c filename=apply_difference.c
int32 apply_difference(int32 (*callback)(int32, int32), int32 left, int32 right) {
    int32 result;
    result = callback(left, right);
    return result;
}
```

```c filename=bad_caller.c
int32 bad_caller() {
    int32 result;
    result = apply_difference(&sum, 40, 2);
    return result;
}
```

```click
verifying "sum.c";
verifying "apply_difference.c";
verifying "bad_caller.c";

contract int32 Difference(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    requires left <= 1000;
    requires right <= 1000;
    ensures result == left - right;
}

int32 sum(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    requires left <= 1000;
    requires right <= 1000;
    ensures result == left + right by auto;
}

int32 apply_difference(int32 (*callback)(int32, int32), int32 left, int32 right) {
    requires Difference(callback);
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    requires left <= 1000;
    requires right <= 1000;
    ensures result == left - right by auto;
}

int32 bad_caller() {
    ensures result == 38 by auto;
}
```

```expect
fail: function `sum` does not satisfy named contract `Difference`
```
