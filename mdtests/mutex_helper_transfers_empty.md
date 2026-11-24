# Direct pthread typedef parameters remain an explicit surface limitation

This frozen C example exercises empty mutex helpers. The current sidecar
parser cannot yet name `pthread_mutex_t` as a parameter type. Keep that
limitation explicit rather than rewriting the C into a containing struct.

```c filename=mutex_helper_transfers_empty.c
#include <pthread.h>
void acquire(pthread_mutex_t *mu) { pthread_mutex_lock(mu); }
void release(pthread_mutex_t *mu) { pthread_mutex_unlock(mu); }
void use(pthread_mutex_t *mu) { acquire(mu); release(mu); }
void run(pthread_mutex_t *mu) {
    pthread_mutex_init(mu, 0);
    acquire(mu);
    release(mu);
    use(mu);
    pthread_mutex_destroy(mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_helper_transfers_empty.c";

void acquire(pthread_mutex_t *mu) {
    owns access: mutex_use(mu);
    produces guard: mutex_guard(mu);
} by {
    let { guard: acquired } = step(pthread_mutex_lock, { access: access });
    step();
    close();
}
void release(pthread_mutex_t *mu) {
    owns access: mutex_use(mu);
    consumes guard: mutex_guard(mu);
} by {
    step(pthread_mutex_unlock, { access: access, guard: guard });
    step();
    close();
}
void use(pthread_mutex_t *mu) {
    owns permission: mutex_use(mu);
} by {
    let { guard: acquired } = step(acquire, { access: permission });
    step(release, { access: permission, guard: acquired });
    step();
    close();
}
void run(pthread_mutex_t *mu) {
    owns mu;
    requires aligned(mu, 8);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init(mu, 0));
    let { guard: acquired } = step(acquire, { access: lifetime });
    step(release, { access: lifetime, guard: acquired });
    step(use, { permission: lifetime });
    step(pthread_mutex_destroy, { lifetime: lifetime });
    step();
    close();
}
```

```expect
fail: the typedef `pthread_mutex_t` stands for a union, or volatile or aligned type
```
