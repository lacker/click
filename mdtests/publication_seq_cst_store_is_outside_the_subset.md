# A sequentially consistent store is outside the publication subset

`memory_order_seq_cst` is at least as strong as release, but the first
atomic subset models only the release/acquire pair, so it is refused rather
than treated as release.

```c filename=publication_seq_cst_store_is_outside_the_subset.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
void *producer(void *argument) {
    struct channel *channel = argument;
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 1, memory_order_seq_cst);
    return NULL;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "publication_seq_cst_store_is_outside_the_subset.c";
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
    close();
}
```

```expect
fail: atomic_store_explicit with memory_order_seq_cst is not supported; one-shot publication uses memory_order_release
```
