# The parent cannot free an anchor whose authority a worker holds

The creator establishes a population on a fresh object and lends its authority
to a worker. This C frees the object before joining the worker. Freeing an
anchor needs every authority on it retired, and the parent cannot retire the
authority the worker holds.

```c filename=modeled_pthread_free_while_lent_rejected.c
#include <pthread.h>
#include <stddef.h>
struct object { int refs; };
void *worker(void *argument) { return NULL; }
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, obj) != 0) {
        free(obj);
        return 0;
    }
    free(obj);
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_free_while_lent_rejected.c";
authorized resource reference(obj: struct object*) {}
void* worker(void* argument) {
    owns authority(reference(argument as (struct object *)));
}
int32 run() {
    ensures result == -1 or result == 0 or result == 1;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    fold(authority(reference(obj)));
    step();
    step();
    branch {
        true => {
            unfold(authority(reference(obj)));
            step();
            step();
            close();
        }
        false => {}
    }
    step();
    step();
    step();
    close();
}
```

```expect
fail: population authority prevents storage
```
