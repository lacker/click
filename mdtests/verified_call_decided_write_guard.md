# A decided call guard determines the loan-separation obligation

The active arm writes the left field and proves separation from a live view
of the right field. The inactive arm can preserve a view of the left field
itself because the call has no write effect.

```c filename=verified_call_decided_write_guard.c
struct pair {
    int left;
    int right;
};

void update_left(struct pair *p, int enabled);

int read_right_when_active(struct pair *p, int enabled) {
    update_left(p, enabled);
    return p->right;
}

int read_left_when_inactive(struct pair *p) {
    update_left(p, 0);
    return p->left;
}
```

```click
resource guarded_left(p: struct pair*, enabled: int32) {
    if enabled != 0 {
        owns p->left;
    }
}

verifying "verified_call_decided_write_guard.c";

extern void update_left(struct pair* p, int32 enabled) {
    owns guarded_left(p, enabled);
}

int32 read_right_when_active(struct pair* p, int32 enabled) {
    requires enabled != 0;
    owns guarded_left(p, enabled);
    views p->right;
    requires separate(memory(p->left), memory(p->right));
    ensures result == old(p->right);
} by {
    step() by { known(); }
}

int32 read_left_when_inactive(struct pair* p) {
    views p->left;
    ensures result == old(p->left);
} by {
    step();
}
```

```expect
pass
```
