# Completing a linked array does not change a shadowing local array

The global has two columns, but the shadowing local has three. Linkage must
complete only the global declaration's selectors.

```c filename=data.c
#include <stdint.h>
const int32_t weights[][2] = {{1}, {2, 3}};
```

```c filename=probe.c
#include <stdint.h>
extern const int32_t weights[][2];
int32_t probe() {
    int32_t weights[1][3] = {{4, 5, 6}};
    return weights[0][2];
}
```

```click
verifying "data.c";
verifying "probe.c";
int32 probe() { ensures result == 6; } by { execute(); simp(); }
```

```expect
pass
```
