# increment with a numeric precondition

This checks that a numeric `requires` clause can rule out signed overflow and
make a symbolic arithmetic postcondition provable.

```c filename=increment.c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures increments: result == x + 1 by auto;
}
```

```expect
pass
```

