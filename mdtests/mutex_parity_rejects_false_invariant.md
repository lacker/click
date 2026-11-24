# The parity loop rejects a false ownership invariant

```c filename=mutex_parity_rejects_false_invariant.c
#include <pthread.h>
#include <stddef.h>

struct parity_mutex {
    pthread_mutex_t mutex;
};

int alternate_mutex(struct parity_mutex *object, int n) {
    if (pthread_mutex_init(&object->mutex, NULL) != 0) return 0;

    int i = 0;
    while (i < n) {
        if (i % 2 == 0) {
            (void)pthread_mutex_lock(&object->mutex);
        } else {
            (void)pthread_mutex_unlock(&object->mutex);
        }
        i++;
    }

    if (i % 2 != 0) (void)pthread_mutex_unlock(&object->mutex);
    (void)pthread_mutex_destroy(&object->mutex);
    return 1;
}
```

```click
import "mutex_parity_lemmas.click";
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_parity_rejects_false_invariant.c";

theorem bounded_one(r: int32) {
    requires 1 <= r;
    requires r <= 1;
    ensures r == 1 by { close() using { 1 <= r; r <= 1; }; }
}

resource loop_guard(object: struct parity_mutex*) {
    field parity: int32;
    if parity == 1 {
        owns mutex_guard(&object->mutex);
    }
}

int32 alternate_mutex(struct parity_mutex *object, int32 n) {
    owns object->mutex;
    requires aligned(&object->mutex, 8);
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    if n < 0 {
        loop {
            decreases n - i;
            invariant i == 0;
            invariant n < 0;
        }
    } else {
        have n >= 0 by close();
        let guard = fold(loop_guard(object), { parity: 0 });
        loop {
            owns guard: loop_guard(object);
            owns mutex_live(&object->mutex);
            decreases n - i;
            invariant 0 <= i and i <= n;
            invariant guard.parity == (i + 1) % 2;
            initialize by close();
            maintain by {
                have i < 2147483647 by { close() using { i < n; }; }
                if i % 2 == 0 {
                    have (i + 1) % 2 == 1 by apply(even_successor(i));
                    have guard.parity == 0 by close();
                    unfold(guard);
                    step();
                    step();
                    step();
                    let guard = fold(loop_guard(object), { parity: 1 });
                } else {
                    have (i + 1) % 2 == 0 by apply(odd_successor(i));
                    have 0 <= i % 2 by { close() using { 0 <= i; }; }
                    have 1 <= i % 2 by apply(nonzero_nonnegative(i % 2));
                    have i % 2 <= 1 by { close() using { 0 <= i; }; }
                    have i % 2 == 1 by apply(bounded_one(i % 2));
                    have guard.parity == 1 by close();
                    unfold(guard);
                    step();
                    step();
                    step();
                    let guard = fold(loop_guard(object), { parity: 0 });
                }
            }
        }
        if i % 2 == 0 {
            have guard.parity == 0 by close();
            unfold(guard);
        } else {
            have 0 <= i % 2 by { close() using { 0 <= i; }; }
            have 1 <= i % 2 by apply(nonzero_nonnegative(i % 2));
            have i % 2 <= 1 by { close() using { 0 <= i; }; }
            have i % 2 == 1 by apply(bounded_one(i % 2));
            have guard.parity == 1 by close();
            unfold(guard);
        }
    }
}
```

```expect
fail: invariant
```
