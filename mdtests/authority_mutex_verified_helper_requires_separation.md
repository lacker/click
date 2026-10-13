# A verified helper borrowing a mutex lifetime still requires separation

A companion of `mutex_abstract_reserved_call.md`. There `touch` is an
assumed contract, which is refused when it moves mutex resources. Here `touch` is a verified helper that borrows the mutex lifetime
and returns it unchanged, so the call is admitted and reaches the same
storage check: the caller's contract must establish that `data` is separate
from the mutex.

```c filename=authority_mutex_verified_helper_requires_separation.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int payload; };
void touch(struct holder *holder, int *data) { *data = 1; }
void write_value(struct holder *holder, int *data) { touch(holder, data); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_verified_helper_requires_separation.c";
void touch(struct holder *holder, int *data) {
    owns mutex_live(&holder->mu);
    owns data[0..1];
    requires separate(memory(data[0..1]), memory(holder->mu));
} by { execute(); simp(); }
void write_value(struct holder *holder, int *data) {
    owns mutex_live(&holder->mu);
    owns data[0..1];
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (touch precondition): separate(data[0], holder[0..10])
```
