# A preserving contract cannot overwrite reserved storage

The mutable footprint is checked at the call boundary even when the helper carries a preserving lifecycle contract.

The unchanged C source currently stops at the frontend limitation on tagged
union stores. Kernel tests exercise the storage-reservation boundary directly.

```c filename=mutex_reserved_helper_write.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
void overwrite(struct holder *holder) { holder->mu.__align = 0; }
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    overwrite(holder);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_reserved_helper_write.c";
void overwrite(struct holder *holder) {
    owns mutex_live(&holder->mu);
    owns &holder->mu;
} by { execute(); simp(); }
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
