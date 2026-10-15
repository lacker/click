# An extern multidimensional array uses its linked definition's outer bound

The reader sees an incomplete declaration; the data translation unit supplies
both rows, including static zero initialization. Completing the executable row
metadata must preserve the checked inner dimension and the actual object bound.

```c filename=data.c
#include <stdint.h>
const int32_t weights[][2] = {{1}, {2, 3}};
```

```c filename=probe.c
#include <stdint.h>
extern const int32_t weights[][2];
int32_t probe() { return weights[0][1] + weights[1][1]; }
```

```click
verifying "data.c";
verifying "probe.c";
int32 probe() { ensures result == 3; } by { execute(); simp(); }
```

```expect
pass
```
