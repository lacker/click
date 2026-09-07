# incomplete external arrays still require a definition

An omitted bound is only a declaration form. The bundle linker must reject an
incomplete external array when no complete fixed-size definition supplies its
storage.

```c filename=include/table.h
extern int32 table[];
```

```c filename=reader.c
#include "include/table.h"

int32 read() {
    return table[0];
}
```

```click
verifying "reader.c";

int32 read() {
    ensures result == 0 by auto;
}
```

```expect
fail: global array `table` is declared `extern` but has no definition
```
