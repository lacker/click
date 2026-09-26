# A second unlock requires a new guard

```c filename=mutex_unlock_twice.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
void wrong(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_unlock_twice.c";
void wrong(struct holder *holder) {
    ensures 0 == 0;
} by {
    step();
    step();
    step();
    step();
}
```

```expect
fail: Requires owns mutex_guard(&holder->mu)
```
