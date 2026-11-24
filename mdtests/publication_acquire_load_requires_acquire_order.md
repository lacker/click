# A receiving load must use acquire order

A relaxed load that observes the flag does not order the payload read
after it. Only `memory_order_acquire` receives the published payload.

```c filename=publication_acquire_load_requires_acquire_order.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
int consume(struct channel *channel) {
    while (atomic_load_explicit(&channel->ready, memory_order_relaxed) == 0) {
    }
    return channel->payload;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "publication_acquire_load_requires_acquire_order.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
int32 consume(struct channel* channel) diverges {
    consumes subscriber(&channel->ready, ready_payload(channel));
    produces ready_payload(channel);
    ensures result == 42;
} by {
    loop diverges {
        owns subscriber(&channel->ready, ready_payload(channel));
    }
    unfold(ready_payload(channel));
    step();
    fold(ready_payload(channel));
    close();
}
```

```expect
fail: atomic_load_explicit with memory_order_relaxed is not supported; one-shot publication uses memory_order_acquire
```
