# The parent cannot retire a population whose authority a worker holds

The creator establishes a population on a fresh object and lends its authority
to a worker. Until join, retiring that population needs the authority, which
the parent no longer owns.

```c filename=modeled_pthread_retire_while_lent_rejected.c
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
    (void)pthread_join(handle, NULL);
    free(obj);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_retire_while_lent_rejected.c";
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
    unfold(authority(reference(obj)));
    step();
    step();
    step();
    close();
}
```

```expect
fail: Requires owns authority(R(p))
```
