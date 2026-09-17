# Minimal spawn and join

```c filename=spawn_minimal.c
#include <pthread.h>
#include <stddef.h>

struct job {
    int value;
};

void *set_seven(void *argument) {
    struct job *job = argument;
    job->value = 7;
    return NULL;
}

int run(struct job *job) {
    pthread_t thread;

    if (pthread_create(&thread, NULL, set_seven, job) != 0) {
        return 0;
    }
    (void)pthread_join(thread, NULL);
    return job->value;
}
```

```click
target "x86_64-linux-userspace";
verifying "spawn_minimal.c";

void *set_seven(void *argument) {
    owns ((struct job *)argument)->value;
    ensures result == 0;
    ensures ((struct job *)argument)->value == 7;
} by {
    execute();
    simp();
}

int32 run(struct job *job) {
    owns job->value;
    ensures result == 0 or result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
