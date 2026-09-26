# Unlock reports the missing guard at its mutex field

```c filename=mutex_unlock_missing_guard.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
void wrong(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_unlock(&holder->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_unlock_missing_guard.c";
void wrong(struct holder *holder) {
    ensures 0 == 0;
} by {
    step();
    step();
}
```

```expect
fail: Requires owns mutex_guard(&holder->mu)
```
