# A linked extern array still rejects a row beyond its definition

The reader's incomplete declaration does not remove the linked object's row
bound. Row two is outside this two-row definition.

```c filename=data.c
#include <stdint.h>
const int32_t weights[][2] = {{1}, {2, 3}};
```

```c filename=probe.c
#include <stdint.h>
extern const int32_t weights[][2];
int32_t probe() { return weights[2][0]; }
```

```click
verifying "data.c";
verifying "probe.c";
int32 probe() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: invalid memory access
```
