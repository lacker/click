# A publication flag must be initialized to zero

A nonzero flag means published. Initializing it nonzero would let a reader
receive a payload no producer has released.

```c filename=publication_flag_must_start_unpublished.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void start(struct channel *channel) {
    atomic_init(&channel->ready, 1);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "publication_flag_must_start_unpublished.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
void start(struct channel* channel) {
    consumes channel->ready;
    owns channel->payload;
    requires aligned(&channel->ready, 4);
} by {
    step(atomic_init, { payload: ready_payload(channel) });
    close();
}
```

```expect
fail: atomic_init of a publication flag stores 0: a nonzero flag means published
```
