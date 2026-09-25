# A loop can retain an unheld mutex across balanced iterations

```c filename=modeled_pthread_held_balanced_loop.c
#include <pthread.h>

struct holder { pthread_mutex_t mu; };

int run(struct holder *holder, int n) {
    int i = 0;
    pthread_mutex_init(&holder->mu, 0);
    while (i < n) {
        pthread_mutex_lock(&holder->mu);
        pthread_mutex_unlock(&holder->mu);
        i++;
    }
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_held_balanced_loop.c";

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
        invariant not held(&holder->mu);
    }
    step();
    simp();
}
```

```expect
pass
```
