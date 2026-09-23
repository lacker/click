# Shared readers may join in reverse order

The parent holds one view of the cell. Each successful creation receives a
distinct reader share; failure of the second creation joins the first child.
On success the second child joins first, then the first child returns the last
outstanding share.

```c filename=modeled_pthread_shared_readers_reverse_join.c
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
    (void)pthread_join(second, NULL);
    (void)pthread_join(first, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_shared_readers_reverse_join.c";

void *reader(void *p) {
    views ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *task) {
    views task->value;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
    step();
    branch {
        then {
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
