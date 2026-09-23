# A parent cannot read a child's output before joining it

Both creates have succeeded, but the first child's mutable cell is still
withheld. Reading it before the corresponding join must fail locally.

```c filename=modeled_pthread_two_create_read_before_join.c
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
    int observed = 0;
    if (pthread_create(&first, NULL, worker, first_task) != 0) {
        return 0;
    }
    if (pthread_create(&second, NULL, worker, second_task) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    observed = first_task->value;
    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    return observed;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_two_create_read_before_join.c";

void *worker(void *p) {
    owns ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *first_task, struct cell *second_task) {
    owns first_task->value;
    owns second_task->value;
    ensures result == 0 or result == 77;
} by {
    step();
    step();
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
}
```

```expect
fail: missing resource fact
```
