# Stack reader shares return in reverse join order

```c filename=modeled_pthread_shared_local_readers_reverse_join.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

void *reader(void *p) {
    struct cell *q = p;
    int observed = q->value;
    return NULL;
}

int run(void) {
    struct cell task = {7};
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, reader, &task) != 0) {
        return 0;
    }
    if (pthread_create(&second, NULL, reader, &task) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    (void)pthread_join(second, NULL);
    (void)pthread_join(first, NULL);
    task.value = 9;
    return task.value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_shared_local_readers_reverse_join.c";

void *reader(void *p) {
    views ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run() {
    ensures result == 0 or result == 9;
} by {
    execute();
    simp();
}
```

```expect
pass
```
