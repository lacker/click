# A retained population unit cannot lend its body outside the lock

The control that owns the counter and the population authority is held by
the mutex. Without acquiring it, the caller has neither, so the helper that
borrows them cannot be called.

```c filename=population_access.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mutex; unsigned int value; };
unsigned int read_member(struct counter *p) { return p->value; }
unsigned int run(struct counter *p) {
    p->value = 3u;
    if (pthread_mutex_init(&p->mutex, NULL) != 0) return 0u;
    
    unsigned int result = read_member(p);
    
    (void)pthread_mutex_destroy(&p->mutex);
    return result;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "population_access.c";
authorized resource member(p: struct counter*) {}
resource control(p: struct counter*) {
    field value: uint32;
    owns p->value;
    owns authority(member(p));
    fact p->value == value;
    fact p->value == count(member(p));
}
uint32 read_member(struct counter* p) {
    owns authority(member(p));
    owns p->value;
    requires p->value == count(member(p));
    ensures result == count(member(p));
    ensures p->value == old(p->value);
}
uint32 run(struct counter* p) {
    owns authority(member(p));
    requires count(member(p)) == 0;
    owns p->value;
    owns p->mutex;
    requires aligned(&p->mutex, 8);
    ensures result == 0 or result == 3;
} by {
    step();
    fold(3 of member(p));
    have count(member(p)) == 3 by close();
    let state = fold(control(p), { value: p->value });
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: state });
    branch { true => { unfold(state); unfold(3 of member(p)); step(); close(); } false => {} }
    step();
    step();
    step(pthread_mutex_destroy, { lifetime: lifetime });
    unfold(state);
    unfold(3 of member(p));
    step();
    close();
}
```

```expect
fail: Requires owns authority(member(...))
```
