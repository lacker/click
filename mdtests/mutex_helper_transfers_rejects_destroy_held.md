# A helper's returned guard still prevents destruction

```c filename=destroy_helper_guard.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void acquire(struct holder *p) { pthread_mutex_lock(&p->mu); }
void run(struct holder *p) {
    pthread_mutex_init(&p->mu, 0);
    acquire(p);
    pthread_mutex_destroy(&p->mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "destroy_helper_guard.c";
void acquire(struct holder *p) {
    owns access: mutex_use(&p->mu);
    produces guard: mutex_guard(&p->mu);
} by {
    step();
    step();
    close();
}
void run(struct holder *p) {
    owns p->mu;
    requires aligned(&p->mu, 8);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init);
    let { guard: acquired } = step(acquire, { access: lifetime });
    step(pthread_mutex_destroy, { lifetime: lifetime });
    step();
    close();
}
```

```expect
fail: cannot destroy a held mutex
```
