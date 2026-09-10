# Integer typed let without parameter

```click
#include <stdint.h>

theorem integer_let_without_parameter() {
    let z: Integer = 184467440737095516160000000000000000001;
    ensures z == 184467440737095516160000000000000000001 by { simp(); }
}
```

```expect
pass
```
