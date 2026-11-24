# An acquire load without the subscriber right receives nothing

The subscriber right is unique, so only one reader receives the payload.
Another reader can still load the flag and see it set, but it gets no
ownership from that.

```c filename=publication_without_subscriber_right_receives_nothing.c
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
struct channel { atomic_int ready; int payload; };
int consume_again(struct channel *channel) {
    while (atomic_load_explicit(&channel->ready, memory_order_acquire) == 0) {
    }
    return channel->payload;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "publication_without_subscriber_right_receives_nothing.c";
resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}
int32 consume_again(struct channel* channel) diverges {
    ensures result == 42;
} by {
    loop diverges {
        invariant channel == channel;
    }
    step();
    close();
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
