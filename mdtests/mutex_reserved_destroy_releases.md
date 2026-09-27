# Destruction releases the storage reservation



The unchanged C source currently stops at the frontend limitation on tagged
union stores. Kernel tests exercise the storage-reservation boundary directly.

```c filename=mutex_reserved_destroy_releases.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_destroy(&holder->mu);
    holder->mu.__align = 0;
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_reserved_destroy_releases.c";
int32 run(struct holder *holder) {
    owns &holder->mu;
    owns holder->value;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: writing tagged union members is not supported
```
