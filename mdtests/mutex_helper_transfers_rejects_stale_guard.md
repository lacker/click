# A releasing helper cannot consume the same acquisition twice

```c filename=stale_helper_guard.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void acquire(struct holder *p) { pthread_mutex_lock(&p->mu); }
void release(struct holder *p) { pthread_mutex_unlock(&p->mu); }
void twice(struct holder *p) { acquire(p); release(p); release(p); }
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "stale_helper_guard.c";
void acquire(struct holder *p) {
    owns access: mutex_use(&p->mu);
    produces guard: mutex_guard(&p->mu);
} by {
    step();
    step();
    close();
}
void release(struct holder *p) {
    owns access: mutex_use(&p->mu);
    consumes guard: mutex_guard(&p->mu);
} by {
    step();
    step();
    close();
}
void twice(struct holder *p) {
    owns access: mutex_use(&p->mu);
} by {
    let { guard: acquired } = step(acquire, { access: access });
    step(release, { access: access, guard: acquired });
    step(release, { access: access, guard: acquired });
    step();
    close();
}
```

```expect
fail: resource proof argument is not owned
```
