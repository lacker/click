# Enum fields in struct values

Named enum fields keep their four-byte ABI representation when a struct is
passed and returned by value. The copy remains independent of the caller's
object, just like a scalar-only struct value.

```c filename=struct_by_value_enum_finish.c
enum packet_state {
    PACKET_READY = 7,
    PACKET_DONE = 9,
};

struct packet {
    int32 count;
    enum packet_state state;
    uint8 tag;
};

struct packet finish(struct packet value) {
    value.count = 5;
    value.state = PACKET_DONE;
    value.tag = 3;
    return value;
}
```

```c filename=struct_by_value_enum_run.c
enum packet_state {
    PACKET_READY = 7,
    PACKET_DONE = 9,
};

struct packet {
    int32 count;
    enum packet_state state;
    uint8 tag;
};

int32 run_struct_by_value_enum() {
    struct packet original;
    struct packet copy;
    original.count = 4;
    original.state = PACKET_READY;
    original.tag = 3;
    copy = finish(original);
    return original.count * 100 + copy.count * 10 + copy.state + original.tag;
}
```

```click
verifying "struct_by_value_enum_finish.c";
verifying "struct_by_value_enum_run.c";

struct packet finish(struct packet value) {
    ensures result.count == 5;
    ensures result.state == 9;
    ensures result.tag == 3;
} by {
    auto;
}

int32 run_struct_by_value_enum() {
    ensures result == 462;
} by {
    execute();
    simp();
}
```

```expect
pass
```
