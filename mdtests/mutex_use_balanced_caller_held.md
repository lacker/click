# A held concrete acquisition blocks a nested use acquisition

```c filename=mutex_use_balanced_caller_held.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_lock(&holder->mu);
    helper(holder);
    pthread_mutex_unlock(&holder->mu);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_use_balanced_caller_held.c";

void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    step();
    step();
    step();
    close();
}
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by {
    step();
    step();
    step(helper);
    step();
    step();
    step();
    close();
}
```

```expect
fail: mutex is already guarded
```
