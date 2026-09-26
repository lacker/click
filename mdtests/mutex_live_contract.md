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
target "x86_64-linux-userspace";
runtime "modeled-pthread";

verifying "mutex_live_contract.c";

void inner(struct holder *holder) {
    owns mutex_live(&holder->mu);
} by { execute(); simp(); }
void keep(struct holder *holder) {
    owns mutex_live(&holder->mu);
} by {
    step(inner(holder), {});
    step();
    simp();
}
int32 run(struct holder *holder) {
    ensures result == 0;
} by {
    step();
    step(keep(holder), {});
    step();
    step();
    simp();
}
```

```expect
pass
```
