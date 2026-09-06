# tentative scalar globals coalesce across translation units

C permits an external scalar declaration without an initializer to be a
tentative definition. Multiple tentative definitions provide one zero-filled
object, and an initialized definition in another translation unit supplies the
value when one exists.

```c filename=include/counters.h
#ifndef COUNTERS_H
#define COUNTERS_H
extern int32 zero_counter;
extern int32 initialized_counter;
int32 bump_counters();
#endif
```

```c filename=tentative.c
#include "include/counters.h"

int32 zero_counter;
int32 initialized_counter;

int32 bump_counters() {
    zero_counter = zero_counter + 1;
    initialized_counter = initialized_counter + 1;
    return initialized_counter;
}
```

```c filename=reader.c
#include "include/counters.h"

int32 zero_counter;
int32 initialized_counter = 7;

int32 read_counters() {
    return zero_counter + initialized_counter;
}

int32 run() {
    return bump_counters();
}
```

```click
verifying "tentative.c";
verifying "reader.c";

int32 bump_counters() {
    mutable &zero_counter[0..1], &initialized_counter[0..1] by auto;
    ensures result == old(initialized_counter) + 1 by auto;
    ensures zero_counter == old(zero_counter) + 1 by auto;
    ensures initialized_counter == old(initialized_counter) + 1 by auto;
}

int32 read_counters() {
    ensures result == 7 by auto;
}

int32 run() {
    mutable &zero_counter[0..1], &initialized_counter[0..1] by auto;
    ensures result == 8 by auto;
}
```

```expect
pass
```
