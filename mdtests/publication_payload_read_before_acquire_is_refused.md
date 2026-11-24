# The payload cannot be read before the flag is acquired

Holding the subscriber right is not holding the payload. Until an acquire
load observes a nonzero flag, the producer may still be writing it.

```c filename=publication_payload_read_before_acquire_is_refused.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
int peek(struct channel *channel) {
    return channel->payload;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "publication_payload_read_before_acquire_is_refused.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
int32 peek(struct channel* channel) {
    owns subscriber(&channel->ready, ready_payload(channel));
} by {
    step();
    close();
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
