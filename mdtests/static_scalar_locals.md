# static scalar locals keep one stable object

A function-local scalar `static` is initialized at function entry, then the
same object is used by every statement in the function. Its contract can name
the object just like a file-scope scalar global.

```c filename=static_scalar_locals.c
int32 increment_twice() {
    static int32 calls = 5;
    calls = calls + 1;
    calls = calls + 1;
    return calls;
}
```

```click
verifying "static_scalar_locals.c";

int32 increment_twice() {
    mutable &calls[0..1] by auto;
    ensures result == old(calls) + 2 by auto;
    ensures calls == old(calls) + 2 by auto;
}
```

```expect
pass
```
