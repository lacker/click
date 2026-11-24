# A call step retains the original state of its array-element bound

A write to `visited` leaves `left` unchanged. The observed resource supplies
the bound at the current state; the call reads the same cell through its
entry state. Keep the call theorem's original bound when transporting its
facts to the statement exit. Instantiate the held entry-state bound
explicitly before the call: simple call checking no longer scans all ambient
conditions for a memory-equivalent spelling.

```c filename=probe.c
int32 probe(int32 *left, int32 *visited, int32 n, int32 cur) {
    visited[cur] = 1;
    return use(left[cur]);
}
```

```click
import click::separation;
verifying "probe.c";
resource bounded(left: int32*, n: int32) {
    views left[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
}
extern int32 use(int32 x) {
    requires 0 <= x;
    ensures result == x;
}
int32 probe(int32 *left, int32 *visited, int32 n, int32 cur) {
    requires 0 <= cur;
    requires cur < n;
    requires n <= 1073741823;
    views bounded(left, n);
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
    ensures result >= 0;
} by {
    have contains(memory(visited[0..n]), memory(visited[cur..cur + 1])) by {
        apply(separation::contains_subrange(visited, 0, n, cur, cur + 1));
    }
    have contains(memory(visited[cur..cur + 1]), memory((visited + cur)[0..1])) by { normalize(); }
    have contains(memory(visited[0..n]), memory((visited + cur)[0..1])) by {
        apply(separation::contains_trans(memory(visited[0..n]), memory(visited[cur..cur + 1]), memory((visited + cur)[0..1])));
    }
    step();
    observe(bounded(left, n));
    have 0 <= left[cur] and left[cur] < n by {
        instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n }, cur);
        close();
    }
    have 0 <= old(left[cur]) by {
        instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n }, cur);
        close();
    }
    let { result: value } = step(use);
    step(); close();
}
```

```expect
pass
```
