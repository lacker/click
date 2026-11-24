# a framed fold equality grants no C read

The proof preserves each prefix read across the endpoint store and uses
induction to recover `zeros(v, 0, i) == 0`. That equality grants no C read
permission. The function owns only the endpoint, so the subsequent
`return v[0]` is refused.

```c filename=fold_read_transport_grants_no_c_read.c
int32 set_then_read(int32 *v, int32 i) {
    v[i] = 1;
    return v[0];
}
```

```click
verifying "fold_read_transport_grants_no_c_read.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem same_zeros(p: int32[], q: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires forall (k: int32) { lo <= k and k < n implies p[k] == q[k] };
    ensures zeros(p, lo, hi) == zeros(q, lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(zeros(p, lo, hi));
            unfold(zeros(q, lo, hi));
            close();
        } else {
            have lo < hi;
            have 0 <= to_integer(hi - 1) by { close(); }
            have to_integer(hi - 1) < to_integer(hi) by { close(); }
            have to_integer(hi - 1) <= to_integer(n) by { close(); }
            apply(ih(hi - 1));
            have to_integer(hi - 1) < to_integer(n) by { close(); }
            have to_integer(lo) <= to_integer(hi - 1) by { close(); }
            have lo <= (hi - 1) and (hi - 1) < n;
            instantiate(forall (k: int32) { lo <= k and k < n implies p[k] == q[k] }, hi - 1);
            have to_integer(hi - 1) < 2147483647 by { close(); }
            unfold(zeros(p, lo, hi));
            unfold(zeros(q, lo, hi));
            rewrite(p[hi - 1], q[hi - 1]);
            close();
        }
    }
}

int32 set_then_read(int32 *v, int32 i) {
    requires 0 < i;
    requires i < 1000;
    requires zeros(v, 0, i) == 0;
    owns v[i..(i + 1)];
} by {
    mark entry;
    step();
    have forall (k: int32) { 0 <= k and k < i implies v[k] == at(entry, v[k]) } by {
        intro(); intro();
        have i != k by { close() using { k < i; }; }
        have separate(memory(v[i]), memory(v[k])) by {
            apply(click::separation::separate_elements(v, i, k));
        }
        have separate(statement(0).footprint, memory(v[k])) by {
            normalize() using { separate(memory(v[i]), memory(v[k])); };
        }
        preserve(memory(v[k]), statement(0));
    }
    have 0 <= i by { close() using { 0 < i; }; }
    have zeros(v, 0, i) == at(entry, zeros(v, 0, i)) by {
        apply(same_zeros(v, at(entry, v), 0, i, i));
    }
    have zeros(v, 0, i) == 0 by { close(); }
    step();
}
```

```expect
fail: missing resource fact `views v[0]`
```
