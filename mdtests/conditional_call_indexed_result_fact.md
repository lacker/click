# A framed graph index in a conditional call fact

C evaluation reuses the graph cell from before the separated store. An explicit
transport equality lets the caller rewrite its post-store historical index to
that evaluated value, including inside another memory read.

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
    step();
    mark entry;
    have at(entry, next[cur]) == old(next[cur]) by {
        have old(next[cur]) == old(next[cur]) by { normalize(); }
        transport(old(next[cur]) == old(next[cur]), at(entry, next[cur]) == old(next[cur])) using {
            old(next[cur]) == old(next[cur]); 0 <= cur; cur < n;
            separate(memory(next[0..n]), memory(visited[0..n]));
        };
        assumption();
    }
    let r = step(visit(next, visited, n, next[cur]), {});
    have r == 0 implies visited[at(entry, next[cur])] != 0 by { rewrite(at(entry, next[cur]) == old(next[cur])); assumption(); }
    branch { then { step(); simp(); } else {} }
    step(); simp();
}
```

```expect
pass
```
