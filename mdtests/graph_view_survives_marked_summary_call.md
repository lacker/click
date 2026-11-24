# A graph view survives a call with a quantified marking summary

```c filename=graph_view_survives_marked_summary_call.c
extern void visit(int32 *left, int32 *visited, int32 n);
void caller(int32 *left, int32 *visited, int32 n) {
    visit(left, visited, n);
}
```

```click
import click::separation;
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
        have 0 <= k; have k < n;
        have contains(memory(left[0..n]), memory(left[k])) by {
            apply(separation::contains_element(left, 0, n, k));
        }
        have contains(memory(visited[0..n]), statement(0).footprint) by { close(); }
        have separate(memory(visited[0..n]), memory(left[0..n])) by {
            apply(separation::separate_symm(memory(left[0..n]), memory(visited[0..n])));
        }
        have separate(statement(0).footprint, memory(left[k])) by {
            apply(separation::separate_restrict(memory(visited[0..n]), memory(left[0..n]), statement(0).footprint, memory(left[k])));
        }
        have left[k] == old(left[k]) by {
            preserve(memory(left[k]), statement(0));
        }
        close();
    }
}
```

```expect
pass
```
