# a foreign static array's call requirement is a statable goal

The precondition of `increment_twice` reads its own function-local `static`
array. A caller can state that requirement itself, ahead of the call, in the
qualified spelling the language already gives it — the same spelling
[surface synthesis](../docs/concepts/expansion.md) recovers for an emitted
call requirement over a foreign static object. An explicitly stated
requirement raises no obligation at the call, so the step's exact routes
discharge it from the stated facts alone.

```c filename=static_local_arrays.c
int32 increment_twice() {
    static int32 values[3] = {5, 7};
    values[0] = values[0] + 1;
    values[0] = values[0] + 1;
    return values[0] + values[1] + values[2];
}

int32 call_twice() {
    int32 first;
    int32 second;
    first = increment_twice();
    second = increment_twice();
    return second;
}
```

```click
verifying "static_local_arrays.c" as static_local;

int32 increment_twice() {
    owns values[0..3];
    requires values[0] > -1000 and values[0] < 1000 and values[1] > -1000 and values[1] < 1000 and values[2] > -1000 and values[2] < 1000;
    ensures result == old(values[0]) + old(values[1]) + old(values[2]) + 2 by auto;
    ensures values[0] == old(values[0]) + 2 by auto;
    ensures values[1] == old(values[1]) by auto;
    ensures values[2] == old(values[2]) by auto;
}

int32 call_twice() {
    owns static_local::increment_twice::values[0..3];
    requires static_local::increment_twice::values[0] == 5 and static_local::increment_twice::values[1] == 7 and static_local::increment_twice::values[2] == 0;
    ensures result == 16;
} by {
    have static_local::increment_twice::values[0] > -1000 by simp;
    have static_local::increment_twice::values[0] < 1000 by simp;
    have static_local::increment_twice::values[1] > -1000 by simp;
    have static_local::increment_twice::values[1] < 1000 by simp;
    have static_local::increment_twice::values[2] > -1000 by simp;
    have static_local::increment_twice::values[2] < 1000 by simp;
    execute();
    simp();
}
```

```expect
pass
```
