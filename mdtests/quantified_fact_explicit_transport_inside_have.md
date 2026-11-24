# Explicit universal preservation inside a C proof's `have`

One source is a bounded-value precondition, as in the DFS search. The other
is a reflexive entry-state fact whose target says every bounded cell of
`next` is unchanged by a store to separate `visited`. The proof introduces each index and applies preservation
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
    }) by { close(); }
    have contains(memory(visited[0..1]), memory(visited[0])) by {
        apply(click::separation::contains_element(visited, 0, 1, 0));
    }
    step();
    have forall (k: int32) {
        0 <= k and k < 2 implies next[k] == at(entry, next[k])
    } by {
        intro(); intro();
        have contains(memory(next[0..2]), memory(next[k])) by {
            apply(click::separation::contains_element(next, 0, 2, k));
        }
        have separate(memory(visited[0]), memory(next[k])) by {
            apply(click::separation::separate_restrict(memory(visited[0..1]), memory(next[0..2]), memory(visited[0]), memory(next[k])));
        }
        have separate(statement(0).footprint, memory(next[k])) by {
            close() using { separate(memory(visited[0]), memory(next[k])); };
        }
        preserve(memory(next[k]), statement(0));
    }
    have forall (k: int32) {
        0 <= k and k < 2 implies 0 <= next[k]
    } by {
        intro(); intro();
        instantiate(forall (j: int32) { 0 <= j and j < 2 implies next[j] == at(entry, next[j]) }, k);
        instantiate(at(entry, forall (j: int32) { 0 <= j and j < 2 implies 0 <= next[j] }), k);
        rewrite(next[k], at(entry, next[k]));
        close();
    }
    have forall (k: int32) {
        0 <= k and k < 2 implies at(entry, next[k]) == next[k]
    } by {
        intro(); intro();
        instantiate(forall (j: int32) { 0 <= j and j < 2 implies next[j] == at(entry, next[j]) }, k);
        close();
    }
}
```

```expect
pass
```
