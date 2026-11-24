# The producer gives up the payload at the release store

The release store hands `ready_payload(channel)` to whoever acquires the
flag. A later write by the producer races with that reader, so it is
refused for lack of ownership.

```c filename=publication_producer_cannot_write_after_release.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void *producer(void *argument) {
    struct channel *channel = argument;
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 1, memory_order_release);
    channel->payload = 7;
    return NULL;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "publication_producer_cannot_write_after_release.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
void* producer(void* argument) {
    consumes publisher(
        &(argument as (struct channel *))->ready,
        ready_payload(argument as (struct channel *))
    );
    consumes (argument as (struct channel *))->payload;
} by {
    step();
    step();
    step();
    fold(ready_payload(channel));
    step();
    step();
    step();
    close();
}
```

```expect
fail: missing resource fact `owns ((char *)argument)[4..8]`
```
