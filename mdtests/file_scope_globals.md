# Scalar globals are shared across C translation units

File-scope scalar definitions provide one stable object. Other C files see the
same object through an `extern` declaration, and Click contracts can name its
address and its entry value.

```c filename=include/counter.h
#ifndef COUNTER_H
#define COUNTER_H
extern int32 counter;
int32 increment_counter();
#endif
```

```c filename=counter.c
#include "include/counter.h"

int32 counter = 3;

int32 increment_counter() {
    counter = counter + 1;
    return counter;
}
```

```c filename=reader.c
#include "include/counter.h"

int32 read_counter() {
    return counter;
}

int32 run() {
    increment_counter();
    return counter;
}
```

```click
verifying "counter.c";
verifying "reader.c";

int32 increment_counter() {
    mutable &counter[0..1] by auto;
    ensures result == old(counter) + 1 by auto;
    ensures counter == old(counter) + 1 by auto;
}

int32 read_counter() {
    ensures result == old(counter) by auto;
}

int32 run() {
    mutable &counter[0..1] by auto;
    ensures result == 4 by auto;
}
```

```expect
pass
```
