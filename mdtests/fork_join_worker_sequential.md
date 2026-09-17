# The fork/join worker verifies once, sequentially, with its task contract

`fill_range` is the worker of the frozen concurrency probe
`design/concurrency-probes/fork_join.c`, byte for byte. Its contract is the
task a future spawn transfers: a stable view of the stack job record, reached
through the opaque `void *` argument by a contract cast, and exclusive
ownership of exactly the job's output slice. This sequential proof establishes
the worker's exact memory effect with no thread rule involved; it is not
evidence that the concurrent parent verifies.

The sidecar selects the probe's user-space target so the source keeps its
`<stddef.h>` include.

```c filename=fill_range.c
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
```

```click
target "x86_64-linux-userspace";
verifying "fill_range.c";

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
```

```expect
pass
```
