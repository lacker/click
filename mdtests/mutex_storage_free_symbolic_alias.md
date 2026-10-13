# A returned pointer can still name an initialized mutex's allocation

This synthetic C regression uses allocator builtins and a modular identity
helper. The returned pointer's symbolic identity must not make the underlying
allocation appear unrelated to the initialized mutex.

```c filename=mutex_storage_free_symbolic_alias.c
#include <pthread.h>
struct holder { int prefix; pthread_mutex_t mu; };
struct holder *identity(struct holder *p) { return p; }
int run(void) {
    struct holder *holder = malloc(sizeof(struct holder));
    if (holder == 0) return 0;
    struct holder *alias = identity(holder);
    pthread_mutex_init(&alias->mu, 0);
    free(holder);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_storage_free_symbolic_alias.c";
struct holder* identity(struct holder* p) {
    ensures result == p;
} by { execute(); simp(); }
int32 run() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: Requires separate(…[0..48], …[0..40])
```
