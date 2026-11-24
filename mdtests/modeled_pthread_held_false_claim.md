# `held` cannot invent mutex guard authority

```c filename=modeled_pthread_held_false_claim.c
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
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_held_false_claim.c";

int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by {
    step();
    step();
    step();
    have held(&holder->mu) by close();
    step();
    close();
}
```

```expect
fail: could not establish `held(byte_offset(holder, 0))`
```
