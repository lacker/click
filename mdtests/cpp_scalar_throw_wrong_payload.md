# C++ scalar throw rejects a false exceptional postcondition

The exceptional outcome carries the thrown value, not a convenient value
selected by the specification.

```cpp filename=throw_seven.cpp function=throw_seven profile=scalar_int32
int throw_seven() { throw 7; }
```

```click
verifying "throw_seven.cpp";

int32 throw_seven() throws int32 {
    ensures result == 0;
    exceptional ensures exception == 8;
}
```

```expect
fail: unclosed goal: exception == 8
```
