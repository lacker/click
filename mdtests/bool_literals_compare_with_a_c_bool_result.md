# `true` and `false` compare with a C `bool` result

`true` and `false` are specification `bool` literals, the C `bool` values `1`
and `0`. A C function returning `bool` can be specified with them, and a
`bool` value written alone where a proposition is expected means
`value == true`, so `ensures result;` and `ensures not result;` state the
same claims as `ensures result == true;` and `ensures result == false;`.

```c filename=bool_result.c
#include <stdbool.h>

bool is_positive(int x) { return x > 0; }
bool is_negative(int x) { return x < 0; }
```

```click
verifying "bool_result.c";

bool is_positive(int32 x) {
    requires x > 0;
    ensures result == true;
    ensures result;
    ensures result != false;
} by {
    execute();
    simp();
}

bool is_negative(int32 x) {
    requires x >= 0;
    ensures result == false;
    ensures not result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
