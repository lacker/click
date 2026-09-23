# A worker reads a fresh local job and writes caller-owned output

The job fields are borrowed for the worker's lifetime. Its output pointer
reaches storage supplied by the caller, so the worker can write the output
while the job loan stays active. The parent recovers the output at join.

```c filename=modeled_pthread_local_job_external_output.c
#include <pthread.h>
#include <stddef.h>

struct job { int *output; int value; };

void *worker(void *argument) {
    struct job *job = argument;
    job->output[0] = job->value;
    return NULL;
}

int run(int output[1]) {
    pthread_t handle;
    struct job job = {output, 11};
    if (pthread_create(&handle, NULL, worker, &job) != 0) {
        return 0;
    }
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_local_job_external_output.c";

void *worker(void *argument) {
    views &((struct job *)argument)->output;
    views ((struct job *)argument)->value;
    owns ((struct job *)argument)->output[0..1];
    requires separate(memory(((struct job *)argument)[0..3]), memory(((struct job *)argument)->output[0..1]));
    ensures ((struct job *)argument)->output[0] == ((struct job *)argument)->value;
} by {
    execute();
    simp();
}

int run(int output[1]) {
    owns output[0..1];
    ensures result == 0 or result == 1;
    ensures result == 1 implies output[0] == 11;
} by {
    execute();
    simp();
}
```

```expect
pass
```
