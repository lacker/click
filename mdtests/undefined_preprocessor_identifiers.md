# Undefined preprocessor identifiers evaluate to zero

```c filename=api.h
#include <inttypes.h>
#if __cplusplus
#include "missing-cplusplus.h"
#endif
#if ABSENT != 0
#include "missing-absent.h"
#endif
uint64_t read_value(void);
```

```c filename=read.c
#if NEVER_DEFINED
#include "missing-root.h"
#endif
#include "api.h"
#define SELECT 1
#undef SELECT
#if SELECT
#include "missing-after-undef.h"
#elif SELECT == 0 && !__cplusplus
uint64_t read_value(void) { return 7ULL; }
#endif
```

```click
verifying "read.c";
uint64_t read_value() { ensures result == 7u64; } by { execute(); simp(); }
```

```expect
pass
```
