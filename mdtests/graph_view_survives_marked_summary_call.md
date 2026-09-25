# A graph view survives a call with a quantified marking summary

```c filename=graph_view_survives_marked_summary_call.c
extern void visit(int32 *left, int32 *visited, int32 n);
void caller(int32 *left, int32 *visited, int32 n) {
    visit(left, visited, n);
}
```

```click
verifying "graph_view_survives_marked_summary_call.c";
resource graph(left: int32*, n: int32) {
    views left[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
}
extern void visit(int32 *left, int32 *visited, int32 n) {
    views graph(left, n);
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
    ensures forall (k: int32) { 0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0 };
}
void caller(int32 *left, int32 *visited, int32 n) {
    views graph(left, n);
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
    ensures forall (k: int32) { 0 <= k and k < n implies old(left[k]) == left[k] };
} by {
    step();
    observe(graph(left, n));
    have forall (k: int32) { 0 <= k and k < n implies old(left[k]) == left[k] } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        have old(left[k]) == old(left[k]) by { normalize(); }
        transport(old(left[k]) == old(left[k]), old(left[k]) == left[k]) using {
            old(left[k]) == old(left[k]);
            0 <= k; k < n;
            separate(memory(left[0..n]), memory(visited[0..n]));
        };
        assumption();
    }
    execute(); simp();
}
```

```expect
pass
```
