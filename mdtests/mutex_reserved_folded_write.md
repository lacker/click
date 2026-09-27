# Folding lifetime ownership does not release reserved bytes



The unchanged C source currently stops at the frontend limitation on tagged
union stores. Kernel tests exercise the storage-reservation boundary directly.

```c filename=mutex_reserved_folded_write.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    holder->mu.__align = 0;
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_reserved_folded_write.c";
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}
int32 run(struct holder *holder) {
    owns &holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by {
    step();
    let life = fold(lifetime(holder), { tag: 0 });
    step();
}
```

```expect
fail: writing tagged union members is not supported
```
