# Lifecycle authority does not grant an acquisition

```c filename=mutex_use_does_not_hold.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void need_guard(struct holder *holder) {}
void inner(struct holder *holder) { need_guard(holder); }
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

verifying "mutex_use_does_not_hold.c";

void need_guard(struct holder *holder) {
    owns mutex_guard(&holder->mu);
}
void inner(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by { step(need_guard); }
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
fail: Requires owns mutex_guard(&holder->mu)
```
