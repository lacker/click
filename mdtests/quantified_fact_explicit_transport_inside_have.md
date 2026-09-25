# Explicit universal transport inside a C proof's `have`

One source is a bounded-value precondition, as in the DFS search. The other
is a reflexive entry-snapshot fact whose target says every bounded cell of
`next` is unchanged by a store to separate `visited`. Both transports run
inside `have` proofs at the post-store frontier.

```c filename=quantified_fact_explicit_transport_inside_have.c
void mark(int32 *next, int32 *visited) {
    visited[0] = 1;
}
```

```click
verifying "quantified_fact_explicit_transport_inside_have.c";

void mark(int32 *next, int32 *visited) {
    views next[0..2];
    owns visited[0..1];
    requires separate(memory(next[0..2]), memory(visited[0..1]));
    requires forall (k: int32) {
        0 <= k and k < 2 implies 0 <= next[k]
    };
    ensures forall (k: int32) {
        0 <= k and k < 2 implies old(next[k]) == next[k]
    };
} by {
    mark entry;
    have at(entry, forall (k: int32) {
        0 <= k and k < 2 implies 0 <= next[k]
    }) by { assumption(); }
    have forall (k: int32) {
        0 <= k and k < 2 implies at(entry, next[k]) == at(entry, next[k])
    } by {
        intro(); intro(); normalize();
    }
    step();
    have forall (k: int32) {
        0 <= k and k < 2 implies 0 <= next[k]
    } by {
        transport(
            at(entry, forall (k: int32) {
                0 <= k and k < 2 implies 0 <= next[k]
            }),
            forall (k: int32) {
                0 <= k and k < 2 implies 0 <= next[k]
            }
        ) using {
            at(entry, forall (k: int32) {
                0 <= k and k < 2 implies 0 <= next[k]
            });
            separate(memory(next[0..2]), memory(visited[0..1]));
        }
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < 2 implies at(entry, next[k]) == next[k]
    } by {
        transport(
            forall (k: int32) {
                0 <= k and k < 2 implies at(entry, next[k]) == at(entry, next[k])
            },
            forall (k: int32) {
                0 <= k and k < 2 implies at(entry, next[k]) == next[k]
            }
        ) using {
            forall (k: int32) {
                0 <= k and k < 2 implies at(entry, next[k]) == at(entry, next[k])
            };
            separate(memory(next[0..2]), memory(visited[0..1]));
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
pass
```
