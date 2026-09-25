# A mutex needs no guarded resource

Initialization, lock, unlock, and return can be verified when the mutex does
not protect a Click resource.

```c filename=modeled_pthread_empty_mutex.c
#include <pthread.h>

struct holder { pthread_mutex_t mu; };

int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_empty_mutex.c";

int32 run(struct holder *holder) {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
