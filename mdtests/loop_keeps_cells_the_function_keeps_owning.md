# A declaring loop keeps the cells the function keeps owning

`clear_span` is the shape of `examples/arena`'s `arena_free`: the loop owns a
`clearing` window over a flag map whose body declares iterated guarded
ownership of `data`, and the C condition reads `span->end` from a descriptor
the function owns and keeps outside the loop.

A loop that declares a resource havocs the memory that resource owns, and an
iterated fact counts every element it could ever hold, here all of
`data[0..n]`. Nothing says the descriptor is apart from that span, so the
loop head used to drop `span->start` and `span->end` with the rest of the
footprint, and every read of them inside the loop, including the ranking
measure, became a fresh load the proof could not relate to the one before
the store (the loop's work budget ran out searching).

The footprint over-approximates what the loop can write. The body holds only
the loop's declared resources and views of what the function keeps, and a
store needs ownership, so a cell the function keeps owning at the loop entry
cannot be written, whatever the footprint covers: the partition at entry
keeps it apart. The head now keeps such cells, and `span->end` reads as the
same value at the iteration entry and the back edge. The store rule that the
argument relies on is pinned by
`mdtests/loop_body_cannot_write_function_owned_cells.md`.

```c filename=loop_keeps_function_owned_cells.c
struct span {
    int32 start;
    int32 end;
};

void clear_span(struct span* span, int32* flags, int32* data, int32 n) {
    int32 i;
    i = span->start;
    while (i < span->end) {
        flags[i] = 0;
        i = i + 1;
    }
}
```

```click
resource clearing(
    flags: int32*,
    data: int32*,
    n: int32,
    start: int32,
    end: int32
) {
    field next: int32;
    owns flags[0..n];
    forall (k: int32) where 0 <= k and k < n {
        if flags[k] == 0 {
            owns data[k..k + 1];
        }
    }
    owns data[next..end];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= n;
    fact n <= 536870911;
    fact separate(memory(flags[0..n]), memory(data[0..n]));
}

verifying "loop_keeps_function_owned_cells.c";

void clear_span(struct span* span, int32* flags, int32* data, int32 n) {
    owns object(span);
    owns w: clearing(flags, data, n, span->start, span->end);
    requires w.next == span->start;
    requires separate(memory(object(span)), memory(flags[0..n]));
} by {
    let { next: first } = unfold(w);
    step();
    step();
    let w = fold(clearing(flags, data, n, span->start, span->end), {
        next: span->start
    });
    loop {
        decreases span->end - i;
        owns w: clearing(flags, data, n, span->start, span->end);
        invariant w.next == i;
        initialize by simp;
        preserve by {
            let { next: m } = unfold(w);
            have m == i by simp;
            have i < span->end by simp;
            have 0 <= span->start by simp;
            have span->start <= i by simp;
            have 0 <= i by {
                apply(int32_le_transitive(0, span->start, i)) using {
                    0 <= span->start;
                    span->start <= i;
                }
            }
            have span->end <= n by simp;
            have i < n by {
                apply(int32_lt_le_transitive(i, span->end, n)) using {
                    i < span->end;
                    span->end <= n;
                }
            }
            mark opened;
            step();
            give(data[i..i + 1]);
            step();
            have span->start <= at(opened, i) + 1 by {
                apply(int32_increment_lower_bound(at(opened, i), span->start, span->end)) using {
                    span->start <= at(opened, i);
                    at(opened, i) < span->end;
                }
            }
            have at(opened, i) + 1 <= span->end by {
                apply(int32_increment_upper_bound(at(opened, i), span->end)) using {
                    at(opened, i) < span->end;
                }
            }
            let w = fold(clearing(flags, data, n, span->start, span->end), {
                next: at(opened, i) + 1
            });
            close_invariants by {
                both {
                    normalize();
                } and {
                    both {
                        arithmetic() using {
                            at(opened, i) < span->end;
                            0 <= at(opened, i);
                            span->end <= n;
                            n <= 536870911;
                        }
                    } and {
                        arithmetic() using {
                            at(opened, i) < span->end;
                            0 <= at(opened, i);
                            span->end <= n;
                            n <= 536870911;
                        }
                    }
                }
            }
        }
    }
    let { next: last } = unfold(w);
    execute();
    let w = fold(clearing(flags, data, n, span->start, span->end), {
        next: last
    });
    simp();
}
```

```expect
pass
```
