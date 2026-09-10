# Read-only contracts may own nothing

A contract that declares no resources owns nothing, so a function that only
reads existing memory remains valid with no clause at all.

```c filename=call_without_ownership_read_only.c
int32 value = 7;

int32 read_value() {
    return value;
}
```

```click
verifying "call_without_ownership_read_only.c";

int32 read_value() {
    requires value == 7;
    ensures result == 7;
}
```

```expect
pass
```
