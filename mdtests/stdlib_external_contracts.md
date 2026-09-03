# standard-library external contracts

The standard library's narrow libc catalog is available without repeating the
declarations in an ordinary sidecar. Each call below is checked against the
catalog contract, including its preconditions and postconditions.

```c filename=stdlib_external_contracts.c
int32 libc_contracts(uint8 destination[], uint8 source[]) {
    int32 length;
    uint8* copied;
    uint8* filled;
    int32 comparison;
    length = strlen(source);
    copied = memcpy(destination, source, 2);
    filled = memset(destination, 7, 2);
    comparison = memcmp(source, source, 2);
    return length;
}
```

```click
verifying "stdlib_external_contracts.c";

int32 libc_contracts(uint8 destination[], uint8 source[]) {
    requires loadable(source[0..3]);
    requires source[0] == '\0';
    owns destination[0..2];
    requires separate(memory(destination[0..2]), memory(source[0..2]));
    ensures result == 0;
}
```

```expect
pass
```
