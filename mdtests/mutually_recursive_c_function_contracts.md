# mutually recursive C functions verify as one contract component

The two contracts are provisional only while both bodies are checked. Neither
rule is published unless both functions certify successfully.

Each call passes `n` unchanged, so for a positive `n` the two functions call
each other forever. Both signatures therefore say `diverges`: the marker is
contagious, and a caller of a marked function must carry it too.

```c filename=even.c
int32 even(int32 n) {
    int32 result;
    if (n <= 0) {
        return 1;
    }
    result = odd(n);
    return result;
}
```

```c filename=odd.c
int32 odd(int32 n) {
    int32 result;
    if (n <= 0) {
        return 0;
    }
    result = even(n);
    return result;
}
```

```click
verifying "even.c";
verifying "odd.c";

int32 even(int32 n) diverges {
    ensures result >= 0 by auto;
}

int32 odd(int32 n) diverges {
    ensures result >= 0 by auto;
}
```

```expect
pass
```
