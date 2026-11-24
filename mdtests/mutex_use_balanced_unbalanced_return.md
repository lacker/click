# A use helper cannot return with its acquisition outstanding

```c filename=mutex_use_balanced_unbalanced_return.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) { pthread_mutex_lock(&holder->mu); }
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_use_balanced_unbalanced_return.c";

void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    step();
    step();
    close();
}
```

```expect
fail: a function cannot return with a held mutex
```
