# Object-like expression macros

Object-like expressions retain their tokens and ordinary C precedence.

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
} by { execute(); simp(); }
```

```expect
pass
```
