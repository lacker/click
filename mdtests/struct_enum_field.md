# Enum fields and named constants

Named enum fields use the supported four-byte scalar ABI shape. Enumerator
names lower to their declared int32 values, so comparisons remain ordinary
checked C expressions while the enum tag stays in imported metadata.

```c filename=struct_enum_field.c
enum packet_state {
    PACKET_IDLE = -1,
    PACKET_READY = 7,
    PACKET_DONE,
};

struct packet {
    uint8 tag;
    enum packet_state state;
    int32 tail;
};

int32 mark_ready(struct packet* packet) {
    packet->state = PACKET_READY;
    return packet->state == PACKET_READY;
}
```

```click
verifying "struct_enum_field.c";

int32 mark_ready(struct packet* packet) {
    requires loadable(packet->state);
    consumes packet->state;

    ensures result == 1;
    produces packet->state;
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
