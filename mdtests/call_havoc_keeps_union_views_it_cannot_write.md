# A call keeps the union views its write set cannot reach

The positive control for `call_havoc_drops_a_union_member_view.md`. The call
writes `g.first.number`; the view of the sibling union member
`g.second.number` in the same object, and of `h.payload.number` in another,
survive it, and the member the call wrote reads as the value the callee
ensures.

```c filename=call_havoc_keeps_union_views.c
union payload {
    int32 number;
    int32* pointer;
};

struct pair {
    union payload first;
    union payload second;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct pair g;
struct packet h;

void set_number(int32* p) {
    *p = 7;
}

int32 read_sibling() {
    set_number(&g.first.number);
    return g.second.number;
}

int32 read_other_object() {
    set_number(&g.first.number);
    return h.payload.number;
}

int32 read_written() {
    set_number(&g.first.number);
    return g.first.number;
}
```

```click
verifying "call_havoc_keeps_union_views.c";

void set_number(int32* p) {
    owns p[0..1];
    ensures p[0] == 7;
} by auto;

int32 read_sibling() {
    owns g.first.number;
    owns g.second.number;
    requires g.second.number == 3;
    ensures result == 3;
} by auto;

int32 read_other_object() {
    owns g.first.number;
    owns h.payload.number;
    requires h.payload.number == 3;
    ensures result == 3;
} by auto;

int32 read_written() {
    owns g.first.number;
    ensures result == 7;
} by auto;
```

```expect
pass
```
