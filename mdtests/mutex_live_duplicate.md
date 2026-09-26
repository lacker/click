# Lifecycle authority cannot be duplicated by folding

```c filename=mutex_live_duplicate.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void keep(struct holder *holder) {}
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    keep(holder);
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}

verifying "mutex_live_duplicate.c";

void keep(struct holder *holder) {
    owns life: lifetime(holder);
} by { unfold(life); fold(life); execute(); simp(); }
int32 run(struct holder *holder) {
    ensures result == 0;
} by {
    step();
    let life = fold(lifetime(holder), { tag: 0 });
    let duplicate = fold(lifetime(holder), { tag: 0 });
    step(keep(holder), { life: life });
    unfold(life);
    execute();
    simp();
}
```

```expect
fail: fold requires ownership of the complete instance body
```
