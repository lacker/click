# An alias cannot initialize reserved mutex bytes



```c filename=mutex_reserved_overlapping_alias.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
struct holder *identity(struct holder *p) { return p; }
int run(struct holder *holder) {
    struct holder *alias = identity(holder);
    pthread_mutex_init(&holder->mu, 0);
    pthread_mutex_init(&alias->mu, 0);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_reserved_overlapping_alias.c";
struct holder* identity(struct holder* p) { ensures result == p; } by { execute(); simp(); }
int32 run(struct holder *holder) {
    owns &holder->mu;
    owns holder->value;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: Requires separate(
```
