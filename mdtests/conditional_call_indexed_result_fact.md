# A framed graph index in a conditional call fact

C evaluation names the graph cell at the state where the call argument is
read. The post-store historical index therefore matches the call fact directly.
Explicit preservation also proves its equality to the entry value.

```c filename=conditional_call_indexed_result_fact.c
extern int32 visit(int32 *next, int32 *visited, int32 n, int32 from);
int32 caller(int32 *next, int32 *visited, int32 n, int32 cur) {
    visited[cur] = 1;
    if (visit(next, visited, n, next[cur])) return 1;
    return 0;
}
```

```click
verifying "conditional_call_indexed_result_fact.c";
extern int32 visit(int32 *next, int32 *visited, int32 n, int32 from) {
    views next[0..n];
    owns visited[0..n];
    requires separate(memory(next[0..n]), memory(visited[0..n]));
    ensures result == 0 implies visited[from] != 0;
}
int32 caller(int32 *next, int32 *visited, int32 n, int32 cur) {
    views next[0..n];
    owns visited[0..n];
    requires 0 <= cur;
    requires cur < n;
    requires separate(memory(next[0..n]), memory(visited[0..n]));
    ensures result == result;
} by {
    have contains(memory(visited[0..n]), memory(visited[cur])) by {
        apply(click::separation::contains_element(visited, 0, n, cur));
    }
    have contains(memory(next[0..n]), memory(next[0..n])) by {
        apply(click::separation::contains_refl(memory(next[0..n])));
    }
    have separate(memory(visited[cur]), memory(next[0..n])) by {
        apply(click::separation::separate_restrict(memory(visited[0..n]), memory(next[0..n]), memory(visited[cur]), memory(next[0..n])));
    }
    step();
    mark entry;
    have at(entry, next[cur]) == old(next[cur]) by {
        have contains(memory(next[0..n]), memory(next[cur])) by {
            apply(click::separation::contains_element(next, 0, n, cur));
        }
        have contains(memory(visited[cur]), memory(visited[cur])) by { apply(click::separation::contains_refl(memory(visited[cur]))); }
        have separate(memory(visited[cur]), memory(next[cur])) by {
            apply(click::separation::separate_restrict(memory(visited[cur]), memory(next[0..n]), memory(visited[cur]), memory(next[cur])));
        }
        have separate(statement(0).footprint, memory(next[cur])) by {
            close() using { separate(memory(visited[cur]), memory(next[cur])); };
        }
        preserve(memory(next[cur]), statement(0));
    }
    let { result: r } = step(visit);
    have r == 0 implies visited[at(entry, next[cur])] != 0 by { close(); }
    branch { true => { step(); close(); } false => {} }
    step(); close();
}
```

```expect
pass
```
