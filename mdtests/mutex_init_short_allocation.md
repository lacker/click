# Initialization needs every byte of mutex storage

This synthetic C regression uses allocator builtins directly.

```c filename=mutex_init_short_allocation.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
int run(void) {
    struct holder *holder = malloc(sizeof(struct holder) - 1);
    if (holder == 0) return 0;
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_destroy(&holder->mu);
    free(holder);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_init_short_allocation.c";
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
