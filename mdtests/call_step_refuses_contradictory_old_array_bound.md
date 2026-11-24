# A retained state bound cannot satisfy a contradictory call requirement

The unchanged array element is nonnegative. Keeping the original call facts
when transporting them must still reject a call requiring it to be negative.

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
    requires x < 0;
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
    let { result: value } = step(use);
    step(); close();
}
```

```expect
fail: unproved obligation: `left[cur] < 0`
```
