# A loop binder's footprint includes the memory its instance owns

`mark_run` marks the cells `[start, end)` of an occupancy map through a
loop that owns a field-bearing `window` instance, and the window owns the
whole map. After the loop the proof tries to carry the value that
`occupied[start]` had before the loop across it with `transport`, which
would let it conclude `start < 0` from `0 <= start` once the loop's own
store is known.

A loop that declares resources havocs the memory those resources own. The
footprint was computed by expanding composites only, and an owned
field-bearing instance (or an iterated ownership fact) contributed nothing,
so the loop was summarized as writing none of the map and the old value
could be retained. The footprint now opens the instance one body layer at its
own fields, as `unfold` does, and an iterated fact contributes the span of the
elements it could hold, so the final lookup must refuse equality with the old
value of a cell the loop writes.

```c filename=loop_binder_instance_footprint_includes_its_memory.c
void mark_run(int32* occupied, int32 capacity, int32 start, int32 end) {
    int32 i;
    occupied[start] = 0;
    i = start;
    while (i < end) {
        occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
resource window(occupied: int32*, capacity: int32, start: int32, end: int32) {
    field next: int32;
    owns occupied[0..capacity];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 1
    };
}

verifying "loop_binder_instance_footprint_includes_its_memory.c";

void mark_run(int32* occupied, int32 capacity, int32 start, int32 end) {
    consumes w: window(occupied, capacity, start, end);
    requires w.next == start;
    requires start < end;
    ensures start < 0;
} by {
    let { next: n0 } = unfold(w);
    have 0 <= start by close();
    have start < capacity by close();
    step();
    step();
    have occupied[start] == 0 by close();
    step();
    let w = fold(window(occupied, capacity, start, end), { next: start });
    mark pre;
    have at(pre, occupied[start]) == 0 by { close(); }
    loop {
        owns w: window(occupied, capacity, start, end);
        invariant w.next == i;
        decreases end - i;
        initialize by close();
        maintain by {
            let { next: m } = unfold(w);
            have m == i by close();
            have i < end by close();
            have start <= m by close();
            have 0 <= m;
            have 0 <= i by {
                rewrite(i, m);
                close();
            }
            have i < capacity;
            mark opened;
            step();
            step();
            have forall (k: int32) {
                start <= k and to_integer(k) < to_integer(at(opened, i) + 1) implies occupied[k] == 1
            } by {
                intro();
                intro();
                have to_integer(k) < to_integer(at(opened, i) + 1);
                if k < at(opened, i) {
                    have k < m by close();
                    have at(opened, occupied[k]) == 1 by {
                        have at(opened, start) <= at(opened, k) and
                                at(opened, k) < at(opened, m);
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, occupied[j]) == at(opened, 1)
                        }, k);
                        close();
                    }
                    have 0 <= k by close();
                    have k != at(opened, i) by { close() using { k < at(opened, i); }; }
                    have at(opened, separate(memory(occupied[i]), memory(occupied[k]))) by {
                        apply(click::separation::separate_elements(occupied, at(opened, i), k));
                    }
                    have separate(loop(0).statement(0).footprint, memory(occupied[k])) by {
                        normalize() using { at(opened, separate(memory(occupied[i]), memory(occupied[k]))); };
                    }
                    have at(loop(0).statement(0).exit, occupied[k]) == at(opened, occupied[k]) by {
                        preserve(memory(occupied[k]), loop(0).statement(0));
                    }
                    have separate(loop(0).statement(1).footprint, memory(occupied[k])) by { normalize() using { }; }
                    have occupied[k] == at(loop(0).statement(1).entry, occupied[k]) by {
                        preserve(memory(occupied[k]), loop(0).statement(1));
                    }
                    close();
                } else {
                    have k <= at(opened, i);
                    have k == at(opened, i);
                    rewrite(k, at(opened, i));
                    normalize();
                }
            }
            have start <= at(opened, i) by {
                rewrite(at(opened, i), m);
                close();
            }
            have to_integer(start) <= to_integer(at(opened, i) + 1);
            have to_integer(at(opened, i) + 1) <= to_integer(end);
            let w = fold(window(occupied, capacity, start, end), {
                next: at(opened, i) + 1
            });
            have 0 <= to_integer(end - at(opened, i) - 1) by {
                close() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= capacity;
                };
            }
            have to_integer(end - at(opened, i) - 1) < to_integer(end - at(opened, i)) by {
                close() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= capacity;
                };
            }
        }
    }
    let { next: n } = unfold(w);
    transport(at(pre, occupied[start]) == 0, occupied[start] == 0) using {
        at(pre, occupied[start]) == 0;
    }
    have n == i by close();
    have n <= end by close();
    have not (n < end) by {
        rewrite(n, i);
        close();
    }
    have n == end;
    have start < n by {
        rewrite(n, end);
        close();
    }
    have start <= start by normalize();
    have occupied[start] == 1 by {
        instantiate(forall (j: int32) {
            start <= j and j < n implies occupied[j] == 1
        }, start);
        close();
    }
    have start < 0 by {
        contradiction(occupied[start] == 1);
    }
}
```

```expect
fail: `transport using` found no frame evidence carrying its source fact
```
