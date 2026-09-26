# A loop may create and destroy a mutex within an iteration

```c filename=modeled_pthread_iteration_local_mutex.c
#include <pthread.h>

struct holder { pthread_mutex_t mu; pthread_mutex_t anchor; };

int run(struct holder *holder, int n) {
    int i = 0;
    pthread_mutex_init(&holder->anchor, 0);
    while (i < n) {
        pthread_mutex_init(&holder->mu, 0);
        pthread_mutex_lock(&holder->mu);
        pthread_mutex_unlock(&holder->mu);
        pthread_mutex_destroy(&holder->mu);
        i++;
    }
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_iteration_local_mutex.c";

int32 run(struct holder *holder, int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result == 0;
} by {
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
