# A stack cell cannot leave scope while a reader still has its share

```c filename=modeled_pthread_shared_local_reader_scope_exit.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

void *reader(void *p) {
    struct cell *q = p;
    int observed = q->value;
    return NULL;
}

int run(void) {
    pthread_t first;
    pthread_t second;
    if (1) {
        struct cell task = {7};
        if (pthread_create(&first, NULL, reader, &task) != 0) {
            return 0;
        }
        if (pthread_create(&second, NULL, reader, &task) != 0) {
            (void)pthread_join(first, NULL);
            return 0;
        }
        (void)pthread_join(first, NULL);
    }
    (void)pthread_join(second, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_shared_local_reader_scope_exit.c";

void *reader(void *p) {
    views ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run() {
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: automatic storage cannot end while a stable loan is active
```
