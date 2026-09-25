# A call's footprint includes the memory of an instance it owns

`set_one` owns a field-bearing `window` instance that owns an occupancy map,
writes one cell of it, and says so. Its caller knew the cell was `0` before
the call and tries to carry that across the call with `transport`, which,
beside the callee's guarantee that the cell is now `1`, proves `start < 0`
from `0 <= start`.

A call havocs the memory the callee's resource-derived frame owns. That
frame was computed by expanding composites only, and an owned field-bearing
instance contributed nothing, so the call was summarized as writing none of
the window's memory and the transport succeeded. The frame now opens the
instance one body layer at its own fields, so the transport has no frame
evidence for a cell the callee may write.

```c filename=call_through_instance_footprint_includes_its_memory.c
void set_one(int32* occupied, int32 capacity, int32 start) {
    occupied[start] = 1;
}

void caller(int32* occupied, int32 capacity, int32 start) {
    occupied[start] = 0;
    set_one(occupied, capacity, start);
}
```

```click
resource window(occupied: int32*, capacity: int32, start: int32) {
    field tag: int32;
    owns occupied[0..capacity];
    fact 0 <= start;
    fact start < capacity;
}

verifying "call_through_instance_footprint_includes_its_memory.c";

void set_one(int32* occupied, int32 capacity, int32 start) {
    owns w: window(occupied, capacity, start);
    ensures w.tag == old(w.tag);
    ensures occupied[start] == 1;
} by {
    let { tag: t } = unfold(w);
    have 0 <= start by simp;
    have start < capacity by simp;
    step();
    have occupied[start] == 1 by simp;
    let w = fold(window(occupied, capacity, start), { tag: t });
    execute();
    simp();
}

void caller(int32* occupied, int32 capacity, int32 start) {
    owns w: window(occupied, capacity, start);
    ensures start < 0;
} by {
    let { tag: t } = unfold(w);
    have 0 <= start by simp;
    have start < capacity by simp;
    step();
    have occupied[start] == 0 by simp;
    let w = fold(window(occupied, capacity, start), { tag: t });
    mark pre;
    step(set_one(occupied, capacity, start), { w: w });
    let { tag: t2 } = unfold(w);
    have occupied[start] == at(pre, occupied[start]) by {
        transport(
            at(pre, occupied[start]) == at(pre, occupied[start]),
            occupied[start] == at(pre, occupied[start])
        ) using {
            0 <= start;
            start < capacity;
        }
    }
    have occupied[start] == 1 by simp;
    have start < 0 by {
        contradiction(occupied[start] == 1);
    }
    let w = fold(window(occupied, capacity, start), { tag: t2 });
    execute();
    simp();
}
```

```expect
fail: `transport using` found no frame evidence
```
