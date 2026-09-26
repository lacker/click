# mutex live rejects destroy contract

```c filename=mutex_live_rejects_destroy_contract.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void destroy(struct holder *holder) { pthread_mutex_destroy(&holder->mu); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_live_rejects_destroy_contract.c";
void destroy(struct holder *holder) { owns mutex_live(&holder->mu); } by { execute(); simp(); }
```

```expect
fail: preserving mutex contracts cannot change mutex protocols
```
