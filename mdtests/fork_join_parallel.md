# The fork/join parent verifies its three creation outcomes

`fill_parallel` is the frozen concurrency probe, byte for byte. Each
`pthread_create` transfers one worker task out of the parent and, on
success, mints a linear completion right; each `pthread_join` consumes that
right and installs the worker's guarantee. The parent's three outcomes are
ordinary status branches: the first creation fails (four zeros), the second
fails after the first succeeded (join the first, then `[11, 11, 0, 0]`), or
both succeed (`[11, 11, 22, 22]`).

```c filename=fork_join.c
#include <pthread.h>
#include <stddef.h>

struct range_job {
    int *output;
    int begin;
    int end;
    int value;
};

void *fill_range(void *argument) {
    struct range_job *job = argument;
    for (int index = job->begin; index < job->end; ++index) {
        job->output[index] = job->value;
    }
    return NULL;
}

int fill_parallel(int output[4]) {
    pthread_t first;
    pthread_t second;
    struct range_job first_job = {output, 0, 2, 11};
    struct range_job second_job = {output, 2, 4, 22};

    for (int index = 0; index < 4; ++index) {
        output[index] = 0;
    }

    if (pthread_create(&first, NULL, fill_range, &first_job) != 0) {
        return 0;
    }
    if (pthread_create(&second, NULL, fill_range, &second_job) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }

    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
verifying "fork_join.c";

resource range_task(job: struct range_job*) {
    views job->output;
    views job->begin;
    views job->end;
    views job->value;
    owns job->output[job->begin..job->end];
    fact 0 <= job->begin;
    fact job->begin <= job->end;
    fact separate(memory(job[0..6]), memory(job->output[job->begin..job->end]));
}

predicate range_filled(job: struct range_job*) {
    forall (k: int32) {
        job->begin <= k and k < job->end implies job->output[k] == job->value
    }
}

void *fill_range(void *argument) {
    consumes range_task((struct range_job *)argument);
    produces range_task((struct range_job *)argument);
    ensures result == 0;
    ensures range_filled((struct range_job *)argument);
} by {
    unfold(range_task((struct range_job *)argument));
    step();
    step();
    step();
    step();
    loop as fill {
        views job->output;
        views job->begin;
        views job->end;
        views job->value;
        owns job->output[job->begin..job->end];
        invariant job->begin <= index and index <= job->end;
        invariant forall (k: int32) {
            job->begin <= k and k < index implies job->output[k] == job->value
        };

        initialize by simp;
        preserve by {
            step();
            step();
            simp();
        }
    }
    step();
    fold(range_task((struct range_job *)argument));
    simp();
}

int32 fill_parallel(int32 output[4]) {
    owns output[0..4];
    ensures result == 0 or result == 1;
    ensures result == 1 implies output[0] == 11 and output[1] == 11
        and output[2] == 22 and output[3] == 22;
} by {
    execute();
    simp();
}
```

```expect
pass
```
