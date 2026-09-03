# Object-like macros reject arbitrary replacement expressions

The initial macro subset accepts only one integer or character literal. A
multi-token replacement must receive a source-positioned diagnostic instead of
being partially expanded.

```c filename=main.c
#define LIMIT (1 + 2)

int32 run() {
    return LIMIT;
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 3;
}
```

```expect
fail: unsupported macro definition
```
