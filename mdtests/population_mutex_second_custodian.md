# A second mutex cannot protect the same population

The population's control is exclusive. Depositing it in a second mutex while
the first is held moves its authority out of the first critical section, so
the helper that borrows that authority cannot be called there.

```c filename=population_access.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mutex; pthread_mutex_t other; unsigned int value; };
unsigned int read_member(struct counter *p) { return p->value; }
unsigned int run(struct counter *p) {
    p->value = 3u;
    if (pthread_mutex_init(&p->mutex, NULL) != 0) return 0u;
    (void)pthread_mutex_lock(&p->mutex);
    pthread_mutex_init(&p->other, NULL);
    unsigned int result = read_member(p);
    (void)pthread_mutex_unlock(&p->mutex);
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
    owns p->other;
    requires aligned(&p->other, 8);
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
    unfold(state);
    let second = fold(control(p), { value: p->value });
    let { lifetime: other } = step(pthread_mutex_init, { state: second });
    step();
    step();
    step();
    step(pthread_mutex_destroy, { lifetime: lifetime });
    step();
    close();
}
```

```expect
fail: Requires owns authority(member(...))
```
