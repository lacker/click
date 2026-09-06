# GNU aligned struct layout

The imported Linux header spelling raises the struct alignment and therefore
adds the corresponding tail padding and nested-field padding.

```c filename=aligned.h
#ifndef ALIGNED_H
#define ALIGNED_H
struct aligned_node {
    int32 value;
} __attribute__((aligned(sizeof(long))));

struct container {
    uint8 tag;
    struct aligned_node node;
};
#endif
```

```c filename=main.c
#include "aligned.h"

int32 sizes() {
    return sizeof(struct aligned_node) + sizeof(struct container);
}
```

```click
verifying "main.c";

int32 sizes() {
    ensures result == 24 by auto;
}
```

```expect
pass
```
