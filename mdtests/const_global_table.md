# const global tables across translation units

This verifies that a file-scope const scalar table keeps read-only storage
when it is referenced from another C translation unit, and that the table
decays to a pointer-to-const parameter view.

```c filename=table.h
extern const int32 table[3];
int32 read_table(const int32 *values);
```

```c filename=table.c
const int32 table[3] = {2, 4, 6};

int32 read_table(const int32 *values) {
    return values[1];
}
```

```c filename=reader.c
#include "table.h"

int32 run() {
    return read_table(table);
}
```

```click
verifying "table.c";
verifying "reader.c";

int32 run() {
    ensures table_value: result == 4 by auto;
}

int32 read_table(const int32 *values) {
    views values[0..3];
    ensures table_value: result == values[1] by auto;
}
```

```expect
pass
```
