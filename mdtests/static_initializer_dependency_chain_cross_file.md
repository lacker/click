# static initializer chains resolve after source-bundle linking

Static address initializers may form a dependency chain across global objects.
The function using the chain can appear before the definitions, and the
definitions can be split across translation units; each address still resolves
to the stable linked object block.

```c filename=include/initializer_chain.h
#ifndef INITIALIZER_CHAIN_H
#define INITIALIZER_CHAIN_H
extern int32 target;
extern int32 *alias;
extern int32 **alias_ref;
int32 read_target();
#endif
```

```c filename=forward.c
#include "include/initializer_chain.h"

int32 run() {
    return *alias;
}

int32 **alias_ref = &alias;
int32 *alias = &target;
```

```c filename=target.c
#include "include/initializer_chain.h"

int32 target = 7;

int32 read_target() {
    return target;
}
```

```click
verifying "forward.c";
verifying "target.c";

int32 run() {
    ensures result == 7 by auto;
}

int32 read_target() {
    ensures result == 7 by auto;
}
```

```expect
pass
```
