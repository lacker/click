# Preserved guard arguments refer to the entry pointer

Changing a C parameter does not change which acquisition the contract returns.

```c filename=guard_parameter.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; };
void change_local(struct counter *counter, struct counter *other) { counter = other; }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "guard_parameter.c";

void change_local(struct counter *counter, struct counter *other) {
    owns mutex_guard(&counter->mu);
} by {
    execute();
    simp();
}
```

```expect
pass
```
