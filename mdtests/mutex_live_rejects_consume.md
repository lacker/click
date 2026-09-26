# mutex live rejects consume

```c filename=mutex_live_rejects_consume.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void keep(struct holder *holder) {}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_live_rejects_consume.c";
void keep(struct holder *holder) { consumes mutex_live(&holder->mu); } by { execute(); simp(); }
```

```expect
fail: mutex authority contracts currently require preserving owned inputs
```
