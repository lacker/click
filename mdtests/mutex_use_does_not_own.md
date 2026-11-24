# Borrowed use does not grant lifecycle ownership

```c filename=mutex_use_does_not_own.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void need_owner(struct holder *holder) {}
void inner(struct holder *holder) { need_owner(holder); }
void keep(struct holder *holder) { inner(holder); }
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    keep(holder);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";

verifying "mutex_use_does_not_own.c";

void need_owner(struct holder *holder) {
    owns mutex_live(&holder->mu);
}
void inner(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by { step(need_owner); }
void keep(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    step(inner);
    step();
    close();
}
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by {
    step();
    step(keep);
    step();
    step();
    close();
}
```

```expect
fail: Requires owns mutex_live(&holder->mu)
```
