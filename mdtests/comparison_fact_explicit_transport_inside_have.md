# Explicit comparison transport inside a C proof's `have`

The entry comparison reads `next[0]`. A store to a separate array cannot
change that read, so the same comparison holds at the post-store frontier.

```c filename=comparison_fact_explicit_transport_inside_have.c
void mark(int32 *next, int32 *visited) {
    visited[0] = 1;
}
```

```click
verifying "comparison_fact_explicit_transport_inside_have.c";

void mark(int32 *next, int32 *visited) {
    views next[0..1];
    owns visited[0..1];
    requires separate(memory(next[0..1]), memory(visited[0..1]));
    requires 0 <= next[0];
    ensures 0 <= next[0];
} by {
    mark entry;
    have at(entry, 0 <= next[0]) by { assumption(); }
    step();
    have 0 <= next[0] by {
        transport(at(entry, 0 <= next[0]), 0 <= next[0]) using {
            at(entry, 0 <= next[0]);
            separate(memory(next[0..1]), memory(visited[0..1]));
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
