# Initialized population observations survive allocation and cleanup

Explicit initialization is a body fact, separate from membership and value
equality. Both results of an unrelated allocation preserve the child's
initialized reads. The final release still discharges the allocation.

```c filename=cleanup.c
struct child { int32 refs; int32 payload; };
void child_init(struct child* obj, int32 payload) {
    obj->refs = 1;
    obj->payload = payload;
}
void child_release(struct child* obj) {
    if (obj->refs == 1) { free(obj); }
    else { obj->refs = obj->refs - 1; }
}
int32 cleanup(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) { return -1; }
    child_init(kid, payload);
    int32* other = malloc(sizeof(int32));
    if (other == 0) { child_release(kid); return -1; }
    child_release(kid);
    free(other);
    return 0;
}
```

```click
resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
}

verifying "cleanup.c";

void child_init(struct child* obj, int32 payload) {
    consumes allocation(obj, sizeof(struct child));
    consumes object(obj);
    produces child_ref(obj);
    ensures obj->payload == payload;
} by {
    execute();
    fold(child_ref(obj));
    simp();
}

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_ref(obj);
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
    ensures old(count(child_ref(obj))) > 1 implies obj->payload == old(obj->payload);
} by {
    if obj->refs == 1 {
        unfold(child_ref(obj));
        execute();
        simp();
    } else {
        open(child_ref(obj)) {
            execute();
        }
        have 1 < old(obj->refs) by {
            arithmetic() using {
                1 <= old(obj->refs);
                old(obj->refs) != 1;
            }
        }
        have old(obj->refs) - 1 >= 1 by {
            apply(int32_above_one_predecessor_is_at_least_one(old(obj->refs))) using {
                1 < old(obj->refs);
            }
        }
        have old(obj->refs) == old(count(child_ref(obj))) by { simp(); }
        have old(count(child_ref(obj))) > 1 by {
            simp() using {
                old(obj->refs) > 1;
                old(obj->refs) == old(count(child_ref(obj)));
            }
        }
        have count(child_ref(obj)) != 0 by {
            arithmetic() using { old(count(child_ref(obj))) > 1; }
        }
        simp();
    }
}

int32 cleanup(int32 payload) {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch { then { step(); simp(); } else {} }
    step();
    step();
    step();
    branch { then { step(); step(); simp(); } else {} }
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
