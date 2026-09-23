# A second create failure cannot abandon the first child

The first create has succeeded on the failing path of the second create. A
return on that path must be refused while its completion right is live.

```c filename=modeled_pthread_second_failure_requires_join.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

void *worker(void *p) {
    struct cell *q = p;
    q->value = 77;
    return NULL;
}

int run(struct cell *first_task, struct cell *second_task) {
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, worker, first_task) != 0) {
        return 0;
    }
    if (pthread_create(&second, NULL, worker, second_task) != 0) {
        return 0;
    }
    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_second_failure_requires_join.c";

void *worker(void *p) {
    owns ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *first_task, struct cell *second_task) {
    owns first_task->value;
    owns second_task->value;
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
        }
        else {}
    }
}
```

```expect
fail: a function cannot return with a live pthread completion right
```
