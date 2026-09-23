# One join does not return the parent's owner while another reader lives

```c filename=modeled_pthread_shared_owned_reader_early_write.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

void *reader(void *p) {
    struct cell *q = p;
    int observed = q->value;
    return NULL;
}

int run(struct cell *task) {
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, reader, task) != 0) {
        return 0;
    }
    if (pthread_create(&second, NULL, reader, task) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    (void)pthread_join(first, NULL);
    task->value = 9;
    (void)pthread_join(second, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_shared_owned_reader_early_write.c";

void *reader(void *p) {
    views ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *task) {
    owns task->value;
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns task[0..1]`
```
