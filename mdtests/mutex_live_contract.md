# Nested contracts preserve lifecycle ownership

```c filename=mutex_live_contract.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void inner(struct holder *holder) {}
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

verifying "mutex_live_contract.c";

void inner(struct holder *holder) {
    owns mutex_live(&holder->mu);
}
void keep(struct holder *holder) {
    owns mutex_live(&holder->mu);
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
pass
```
