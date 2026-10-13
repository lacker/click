# One increment cannot produce two contributions

The worker contract claims two contributions for its single increment and
single credit. Only one is created under the authority, so the produced
resources are missing.

```c filename=mutex_counter_doubled_contribution_rejected.c
#include <pthread.h>
#include <stddef.h>

struct mutex_counter {
    pthread_mutex_t mutex;
    unsigned int value;
};

void *increment_counter(void *argument) {
    struct mutex_counter *counter = argument;
    (void)pthread_mutex_lock(&counter->mutex);
    counter->value = counter->value + 1u;
    (void)pthread_mutex_unlock(&counter->mutex);
    return NULL;
}

int increment_twice(struct mutex_counter *counter) {
    pthread_t first;
    pthread_t second;

    counter->value = 0u;
    if (pthread_mutex_init(&counter->mutex, NULL) != 0) return 0;
    if (pthread_create(&first, NULL, increment_counter, counter) != 0) {
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }
    if (pthread_create(&second, NULL, increment_counter, counter) != 0) {
        (void)pthread_join(first, NULL);
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }

    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    (void)pthread_mutex_destroy(&counter->mutex);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_counter_doubled_contribution_rejected.c";

// Each worker that has incremented the counter holds one contribution, and
// each worker still to run holds one credit. The control owns the counter and
// both authorities, so the counter equals the number of contributions and the
// two populations together stay at two.
authorized resource contribution(counter: struct mutex_counter*) {}
authorized resource credit(counter: struct mutex_counter*) {}

resource counter_control(counter: struct mutex_counter*) {
    field done: int32;
    field slack: int32;
    owns counter->value;
    owns authority(contribution(counter));
    owns authority(credit(counter));
    fact to_integer(counter->value) == to_integer(done);
    fact done == count(contribution(counter));
    fact slack == count(credit(counter));
    fact to_integer(done) + to_integer(slack) == 2;
}

void* increment_counter(void* argument) {
    owns access: mutex_use(
        &((struct mutex_counter*)argument)->mutex,
        counter_control((struct mutex_counter*)argument)
    );
    consumes credit((struct mutex_counter*)argument);
    produces 2 of contribution((struct mutex_counter*)argument);
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(
        pthread_mutex_lock(&counter->mutex), { access: access }
    );
    let { done: done, slack: slack } = unfold(state);
    have count(credit(counter)) >= 1;
    have slack == count(credit(counter));
    have 1 <= slack;
    have to_integer(1) <= to_integer(slack) by apply(int32_less_equal_to_integer(1, slack));
    have to_integer(done) <= to_integer(1) by arithmetic() using {
        to_integer(done) + to_integer(slack) == 2;
        to_integer(1) <= to_integer(slack);
    };
    have done <= 1 by apply(int32_to_integer_less_equal_implies_less_equal(done, 1));
    have defined(done + 1);
    have defined(slack - 1);
    have to_integer(done + 1) == to_integer(done) + to_integer(1) by {
        apply(int32_add_to_integer(done, 1));
    }
    have to_integer(slack - 1) == to_integer(slack) - to_integer(1) by {
        apply(int32_subtract_to_integer(slack, 1));
    }
    have to_integer(done + 1) + to_integer(slack - 1) == 2 by arithmetic() using {
        to_integer(done + 1) == to_integer(done) + to_integer(1);
        to_integer(slack - 1) == to_integer(slack) - to_integer(1);
        to_integer(done) + to_integer(slack) == 2;
    };
    have to_integer(counter->value) + to_integer(1u32) <= 4294967295 by arithmetic() using {
        to_integer(counter->value) == to_integer(done);
        to_integer(done) <= to_integer(1);
    };
    have to_integer(counter->value + 1u32) == to_integer(counter->value) + to_integer(1u32) by {
        apply(uint32_add_to_integer(counter->value, 1u32));
    }
    have to_integer(counter->value + 1u32) == to_integer(done + 1) by arithmetic() using {
        to_integer(counter->value + 1u32) == to_integer(counter->value) + to_integer(1u32);
        to_integer(counter->value) == to_integer(done);
        to_integer(done + 1) == to_integer(done) + to_integer(1);
    };
    unfold(credit(counter));
    fold(contribution(counter));
    step();
    let restored = fold(counter_control(counter), { done: done + 1, slack: slack - 1 });
    step(pthread_mutex_unlock(&counter->mutex), {
        access: access, guard: guard, state: restored
    });
    step();
    simp();
}

int32 increment_twice(struct mutex_counter* counter) {
    owns counter->mutex;
    requires aligned(&counter->mutex, 8);
    owns counter->value;
    owns authority(contribution(counter));
    owns authority(credit(counter));
    requires count(contribution(counter)) == 0;
    requires count(credit(counter)) == 0;
    ensures result == 0 or result == 1;
    ensures result == 0 or counter->value == 2u32;
} by {
    step();
    step();
    step();
    fold(credit(counter));
    fold(credit(counter));
    have to_integer(0) + to_integer(2) == 2;
    have to_integer(counter->value) == to_integer(0);
    let state = fold(counter_control(counter), { done: 0, slack: 2 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&counter->mutex, 0), { state: state });
    branch then {
        unfold(state);
        unfold(credit(counter));
        unfold(credit(counter));
        step();
        simp();
    } else {}
    step();
    branch then {
        step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
        unfold(state);
        unfold(credit(counter));
        unfold(credit(counter));
        step();
        simp();
    } else {}
    step();
    branch then {
        step();
        step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
        unfold(state);
        unfold(contribution(counter));
        unfold(credit(counter));
        step();
        simp();
    } else {}
    step();
    step();
    step(pthread_mutex_destroy(&counter->mutex), { lifetime: lifetime });
    let { done: done, slack: slack } = unfold(state);
    have count(contribution(counter)) == 2;
    have done == 2;
    have done <= 2;
    have 2 <= done;
    have to_integer(done) <= to_integer(2) by apply(int32_less_equal_to_integer(done, 2));
    have to_integer(2) <= to_integer(done) by apply(int32_less_equal_to_integer(2, done));
    have to_integer(2) == 2;
    have to_integer(done) == 2 by arithmetic() using {
        to_integer(done) <= to_integer(2);
        to_integer(2) <= to_integer(done);
        to_integer(2) == 2;
    };
    have to_integer(counter->value) == to_integer(done);
    have to_integer(counter->value) == 2 by arithmetic() using {
        to_integer(counter->value) == to_integer(done);
        to_integer(done) == 2;
    };
    have to_integer(2u32) == 2;
    have to_integer(counter->value) == to_integer(2u32) by arithmetic() using {
        to_integer(counter->value) == 2;
        to_integer(2u32) == 2;
    };
    have counter->value == 2u32 by apply(uint32_to_integer_equal_implies_equal(counter->value, 2u32));
    unfold(contribution(counter));
    unfold(contribution(counter));
    step();
    simp();
}
```

```expect
fail: `increment_counter.produces_0` unproved
```
