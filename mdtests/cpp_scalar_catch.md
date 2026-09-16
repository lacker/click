# C++ scalar catch

The helper can return or throw an `int`. The caller catches that exception,
turning both paths into a normal result. This mdtest imports the C++ source
through the pinned compiler frontend; the C parser never sees it.

```cpp filename=caller.cpp function=caller profile=scalar_int32
int helper(bool should_throw) {
    if (should_throw) { throw 7; }
    return 7;
}

int caller(bool should_throw) {
    try { helper(should_throw); }
    catch (int caught) { return caught; }
    return 7;
}
```

```click
verifying "caller.cpp";

int32 helper(bool should_throw) throws int32 {
    ensures result == 7;
    exceptional ensures exception == 7;
}

int32 caller(bool should_throw) {
    ensures result == 7;
}
```

```expect
pass
```
