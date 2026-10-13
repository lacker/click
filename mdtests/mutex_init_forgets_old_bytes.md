# Reading initialized mutex bytes: pointer-retyping limitation

This synthetic C regression uses allocator builtins directly. Owning the
storage permits initialization, but does not preserve the old byte values.
The current frontend rejects the unchanged representation cast before this
claim can be checked; kernel coverage tests the byte invalidation directly.

```c filename=mutex_init_forgets_old_bytes.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
int run(void) {
    struct holder *holder = malloc(sizeof(struct holder));
    if (holder == 0) return 0;
    unsigned char *bytes = (unsigned char *)holder;
    bytes[0] = 17;
    pthread_mutex_init(&holder->mu, 0);
    int value = bytes[0];
    pthread_mutex_destroy(&holder->mu);
    free(holder);
    return value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_init_forgets_old_bytes.c";
int32 run() { ensures result == 0 or result == 17; } by { execute(); simp(); }
```

```expect
fail: retyping object-pointer casts are unsupported
```
