# An incompatible read in a loop condition is refused

A pointer local keeps the class of the object it designates across the
abstract loop iteration, as it keeps its subobject. Here `q` reaches a
`long` through a `void *` round trip, and every evaluation of the loop
condition reads it as `long long`, which C11 6.5p7 does not allow.

```c filename=loop.c
int uprec(int a, long *p) {
    void *v = p;
    long long *q = v;
    while (a != 0 && q[0] != 0) {
        a = 0;
    }
    return a;
}
```

```click
verifying "loop.c";

int32 uprec(int32 a, int64* p) {
    requires a >= 0;
    requires a <= 10;
    views p[0..1];
    ensures result >= 0;
    ensures result <= 10;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases a;
        invariant a >= 0;
        invariant a <= 10;
        maintain by {
            have 0 < a by { close() using { a >= 0; a != 0; }; }
            step();
        }
    }
    step();
    close();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
