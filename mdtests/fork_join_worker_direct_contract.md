# The frozen worker verifies with direct borrowed and owned clauses

The C worker is unchanged from `design/concurrency-probes/fork_join.c`.
Direct `views` clauses allow a future caller to lend its job record while
transferring the output slice. Certificate synthesis must spell the output
pointer through the cast `void *` parameter or the struct-pointer local,
including when checking an expanded quantified readability proof.

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

predicate range_filled(job: struct range_job*) {
    forall (k: int32) {
        job->begin <= k and k < job->end implies job->output[k] == job->value
    }
}

void *fill_range(void *argument) {
    views ((struct range_job *)argument)->output;
    views ((struct range_job *)argument)->begin;
    views ((struct range_job *)argument)->end;
    views ((struct range_job *)argument)->value;
    owns ((struct range_job *)argument)->output[((struct range_job *)argument)->begin..((struct range_job *)argument)->end];
    requires 0 <= ((struct range_job *)argument)->begin;
    requires ((struct range_job *)argument)->begin <= ((struct range_job *)argument)->end;
    requires 0 <= ((struct range_job *)argument)->end - ((struct range_job *)argument)->begin;
    requires ((struct range_job *)argument)->end - ((struct range_job *)argument)->begin <= 1073741823;
    requires separate(memory(((struct range_job *)argument)[0..6]), memory(((struct range_job *)argument)->output[((struct range_job *)argument)->begin..((struct range_job *)argument)->end]));
    ensures result == 0;
    ensures range_filled((struct range_job *)argument);
} by {
    step();
    step();
    step();
    step();
    loop as fill {
        decreases job->end - index;
        views job->output;
        views job->begin;
        views job->end;
        views job->value;
        owns job->output[job->begin..job->end];
        invariant job->begin <= index and index <= job->end;
        invariant forall (k: int32) {
            job->begin <= k and k < index implies job->output[k] == job->value
        };

        initialize by {
            have job->begin <= index and index <= job->end by {
                both { normalize(); } and { assumption(); }
            }
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                contradiction(job->begin <= k and k < index);
            }
        }
        preserve by {
            mark iteration;
            step();
            step();
            have 0 <= at(iteration, index) by {
                simp() using {
                    0 <= job->begin;
                    job->begin <= at(iteration, index);
                }
            }
            have 0 <= job->end by {
                simp() using {
                    0 <= job->begin;
                    job->begin <= job->end;
                }
            }
            have 0 <= 0 - at(iteration, index) + job->end - 1 by {
                arithmetic() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                }
            }
            have 0 - at(iteration, index) + job->end - 1
                < 0 - at(iteration, index) + job->end by {
                arithmetic() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                }
            }
            simp();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
