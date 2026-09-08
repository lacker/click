# Kernel target predefines select the same header during discovery and expansion

```c filename=main.c
#if defined(__CHAR_UNSIGNED__) && __CHAR_BIT__ == 8 && __SIZEOF_POINTER__ == 8
#include "unsigned.h"
#else
#include "unsupported-target.h"
#endif
int selected(void) { return TARGET_VALUE; }
```

```c filename=unsigned.h
#if defined(__KERNEL__) && defined(__x86_64__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define TARGET_VALUE 8
#else
#error wrong target
#endif
```

```click
verifying "main.c";
int selected() { ensures result == 8; } by { execute(); simp(); }
```

```expect
pass
```
