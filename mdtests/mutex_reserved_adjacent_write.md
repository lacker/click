# Adjacent payload remains writable



```c filename=mutex_reserved_adjacent_write.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    holder->value = 17;
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_reserved_adjacent_write.c";
int32 run(struct holder *holder) {
    owns &holder->mu;
    owns holder->value;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
