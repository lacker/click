# A nonfinal counted release preserves the underlying allocation

A caller may consume its last owned unit while other counted units remain.
The callee's post-count keeps the population body allocation live, so the
caller's guarded payload guarantee remains readable.

```c filename=counted_release_preserves_nonfinal_allocation.c
struct child { int32 refs; int32 payload; };

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void release_one(struct child* obj) {
    child_release(obj);
}
```

```click
resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
}


verifying "counted_release_preserves_nonfinal_allocation.c";

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


void release_one(struct child* obj) {
    requires 1 < obj->refs;
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    have obj->refs == count(child_ref(obj)) by { simp(); }
    have 1 < count(child_ref(obj)) by { simp(); }
    step(child_release(obj), {});
    have count(child_ref(obj)) != 0 by { simp(); }
    have obj->payload == old(obj->payload) by { simp(); }
    step();
    simp();
}
```

```expect
pass
```
