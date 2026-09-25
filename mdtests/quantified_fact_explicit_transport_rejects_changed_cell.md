# A quantified fact cannot cross a store to one of its cells

The entry fact allows `a[0]` to be nonnegative. The C store makes it negative,
so transport must refuse the same universal at the post-store frontier.

```c filename=quantified_fact_explicit_transport_rejects_changed_cell.c
void clear(int32 *a) {
    a[0] = -1;
}
```

```click
verifying "quantified_fact_explicit_transport_rejects_changed_cell.c";

void clear(int32 *a) {
    owns a[0..1];
    requires forall (k: int32) {
        0 <= k and k < 1 implies 0 <= a[k]
    };
    ensures forall (k: int32) {
        0 <= k and k < 1 implies 0 <= a[k]
    };
} by {
    mark entry;
    have at(entry, forall (k: int32) {
        0 <= k and k < 1 implies 0 <= a[k]
    }) by { assumption(); }
    step();
    have forall (k: int32) {
        0 <= k and k < 1 implies 0 <= a[k]
    } by {
        transport(
            at(entry, forall (k: int32) {
                0 <= k and k < 1 implies 0 <= a[k]
            }),
            forall (k: int32) {
                0 <= k and k < 1 implies 0 <= a[k]
            }
        ) using {
            at(entry, forall (k: int32) {
                0 <= k and k < 1 implies 0 <= a[k]
            });
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: `transport using` found no frame evidence
```
