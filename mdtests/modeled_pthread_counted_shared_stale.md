# A stale count is false after both members are spent

```c filename=modeled_pthread_counted_shared_stale.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
int run(void *p, void *q) {
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, worker, p) != 0) return 0;
    if (pthread_create(&second, NULL, worker, p) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    (void)pthread_join(second, NULL);
    (void)pthread_join(first, NULL);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_shared_stale.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns ticket(argument);
}
int32 run(void* p, void* q) {
    owns authority(ticket(p));
    owns authority(ticket(q));
    consumes 2 of ticket(p);
    owns ticket(q);
    requires p != q;
    requires count(ticket(p)) == 2;
    requires count(ticket(q)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    branch {
        true => {
            have count(ticket(p)) == 2;
            unfold(ticket(p));
            unfold(ticket(p));
            step(); close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step();
            unfold(ticket(p));
            unfold(ticket(p));
            have count(ticket(q)) == 1;
            step(); close();
        }
        false => {}
    }
    step();
    unfold(ticket(p));
    step();
    unfold(ticket(p));
    have count(ticket(p)) == 2;
    step(); close();
}
```

```expect
fail: could not establish `to_integer(count(ticket(p))) == 2`
```
