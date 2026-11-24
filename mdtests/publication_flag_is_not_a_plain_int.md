# An initialized publication flag is not written as a plain int

`atomic_init` takes the flag's storage: from then on it is accessed only
through the publication rights, and a plain store races with the atomic
operations of other threads.

```c filename=publication_flag_is_not_a_plain_int.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void start(struct channel *channel) {
    atomic_init(&channel->ready, 0);
    *(int *)&channel->ready = 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "publication_flag_is_not_a_plain_int.c";
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
    step();
    close();
}
```

```expect
fail: missing resource fact
```
