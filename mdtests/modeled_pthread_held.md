# `held` reads the current path's mutex guard

```c filename=modeled_pthread_held.c
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
verifying "modeled_pthread_held.c";

int32 run(struct holder *holder) {
    ensures result == 0;
} by {
    step();
    step();
    have held(&holder->mu) by simp;
    step();
    have not held(&holder->mu) by simp;
    step();
    simp();
}
```

```expect
pass
```
