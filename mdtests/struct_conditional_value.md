# Conditional struct values

Supported struct values can be selected with C's conditional operator. The
condition is evaluated first, exactly one branch is copied into fresh
address-backed storage, and the resulting aggregate can be assigned, passed
to a function, or returned by value.

```c filename=struct_conditional_return.c
struct inner {
    int32 value;
    uint8 enabled;
};

struct packet {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

struct packet choose_packet(int32 choose_left, struct packet left, struct packet right) {
    return choose_left ? left : right;
}
```

```c filename=struct_conditional_sum.c
struct inner {
    int32 value;
    uint8 enabled;
};

struct packet {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

int32 sum_packet(struct packet packet) {
    return packet.tag + packet.inner.value + packet.inner.enabled + packet.tail;
}
```

```c filename=struct_conditional_value.c
struct inner {
    int32 value;
    uint8 enabled;
};

struct packet {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

int32 struct_conditional_value() {
    struct packet left = {3, {4, 1}, 5};
    struct packet right = {20, {30, 2}, 40};
    struct packet selected = 0 ? left : right;
    struct packet other;
    other = 1 ? left : right;
    struct packet returned = choose_packet(1, left, right);
    int32 selected_sum = sum_packet(0 ? left : right);

    selected.tag = 99;
    int32 selected_value = sum_packet(selected);
    int32 other_value = sum_packet(other);
    int32 returned_value = sum_packet(returned);
    return selected_sum + selected_value + other_value + returned_value;
}
```

```click
verifying "struct_conditional_return.c";
verifying "struct_conditional_sum.c";
verifying "struct_conditional_value.c";

struct packet choose_packet(int32 choose_left, struct packet left, struct packet right) {
    ensures choose_left == 0 implies result.tag == right.tag;
    ensures choose_left != 0 implies result.tag == left.tag;
    ensures choose_left == 0 implies result.inner.value == right.inner.value;
    ensures choose_left != 0 implies result.inner.value == left.inner.value;
    ensures choose_left == 0 implies result.inner.enabled == right.inner.enabled;
    ensures choose_left != 0 implies result.inner.enabled == left.inner.enabled;
    ensures choose_left == 0 implies result.tail == right.tail;
    ensures choose_left != 0 implies result.tail == left.tail;
} by {
    auto;
}

int32 sum_packet(struct packet packet) {
    views packet->tag;
    views packet->inner.value;
    views packet->inner.enabled;
    views packet->tail;
    requires packet.inner.value >= -1000;
    requires packet.inner.value <= 1000;
    requires packet.tail >= -1000;
    requires packet.tail <= 1000;
    ensures result == packet.tag + packet.inner.value + packet.inner.enabled + packet.tail;
} by {
    auto;
}

int32 struct_conditional_value() {
    ensures result == 289;
} by {
    execute();
    simp();
}
```

```expect
pass
```
