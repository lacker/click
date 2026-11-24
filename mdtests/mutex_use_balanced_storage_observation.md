# A live mutex's representation bytes cannot be read

Initialization consumed ownership of the storage, so no observation of its
bytes exists to preserve across a use call.

```c filename=mutex_use_balanced_storage_observation.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    unsigned char *bytes = (unsigned char *)&holder->mu;
    int before = bytes[0];
    helper(holder);
    int after = bytes[0];
    pthread_mutex_destroy(&holder->mu);
    return before == after;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_use_balanced_storage_observation.c";
void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
}
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    step(helper);
    step();
    step();
    step();
    step();
    close();
}
```

```expect
fail: missing resource fact `views ((char *)holder)[0]`
```
