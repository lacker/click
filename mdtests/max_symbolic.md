# symbolic max verifies on both branches

This checks that `auto` verifies an `ensures` clause across every symbolic
branch, using path facts from the `if`.

```c filename=max.c
int32 max(int32 a, int32 b) {
    if (a < b) {
        return b;
    } else {
        return a;
    }
}
```

```click
verifying "max.c";

int32 max(int32 a, int32 b) {
    ensures result >= a by auto;
    ensures result >= b by auto;
}
```

```expect
pass
```

