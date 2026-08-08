# counted resources are atomic

The first counted-resource model counts atomic capabilities. A composite body
would need a law relating several copies of the abstract resource to several
copies of every body component, so it is rejected rather than given an
accidental meaning.

```c filename=counted_composite.c
int32 counted_composite(int32 value) {
    return value;
}
```

```click
counted resource counted_wrapper(value: int32) {
    fact value == value;
}

verifying "counted_composite.c";

int32 counted_composite(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: a `counted resource` declaration must end with `;`
```
