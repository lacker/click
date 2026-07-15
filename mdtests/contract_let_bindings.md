# Contract Let Bindings

```c filename=bounded_increment.c
int32 bounded_increment(int32 x) {
    return x + 1;
}
```

```c filename=read_first.c
int32 read_first(int32 p[]) {
    return p[0];
}
```

```click
verifying "bounded_increment.c";
verifying "read_first.c";

function inc_with_let(int32 x) -> int32 {
    let next: int32 = x + 1;
    next
}

int32 bounded_increment(int32 x) {
    let max: int32 = 2147483647;
    let expected = x + 1;

    requires x < max;
    ensures result_value: result == expected by auto;
    ensures function_value: result == inc_with_let(x) by simp;
}

int32 read_first(int32 p[]) {
    let len: int32 = 1;
    let first = len - 1;

    requires loadable(p[0..len]);
    views p[0..len];
    ensures result_value: result == p[first] by auto;
}
```

```expect
pass
```
