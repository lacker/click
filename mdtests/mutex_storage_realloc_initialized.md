# Reallocation cannot move initialized mutex storage

This C0 fixture uses the allocator builtins directly; the unsupported
`stdlib.h` include is omitted. The modeled pthread declarations are retained.


```c filename=mutex_storage_realloc_initialized.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
int run(void) {
    struct holder *holder = malloc(sizeof(struct holder));
    if (holder == 0) return 0;
    pthread_mutex_init(&holder->mu, 0);
    struct holder *next = realloc(holder, 2 * sizeof(struct holder));
    if (next == 0) free(holder);
    else free(next);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_storage_realloc_initialized.c";
int32 run() {
    ensures result == 0 by auto;
}
```

```expect
fail: Cannot release allocation
```
