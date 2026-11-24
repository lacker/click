# A fold through a helper survives a store at its exclusive endpoint

The fold calls `cell` at each prefix index. The proof separates each prefix
cell from the store at `i`, preserves its read, and uses induction to show
that the fold through the helper returns the same value at both points.

```c filename=fold_read_transport_rejects_an_opaque_helper.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_rejects_an_opaque_helper.c";

function cell(v: int32[], k: int32) -> Integer {
    to_integer(v[k])
}

function through(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + cell(v, k) })
}

theorem same_through(p: int32[], q: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires viewable(p[0..n]);
    requires viewable(q[0..n]);
    requires forall (k: int32) { lo <= k and k < n implies p[k] == q[k] };
    ensures through(p, lo, hi) == through(q, lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(through(p, lo, hi));
            unfold(through(q, lo, hi));
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
            unfold(through(p, lo, hi));
            unfold(through(q, lo, hi));
            unfold(cell(p, hi - 1));
            unfold(cell(q, hi - 1));
            rewrite(p[hi - 1], q[hi - 1]);
            close();
        }
    }
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures through(v, 0, i) == old(through(v, 0, i));
} by {
    mark entry;
    have viewable(v[0..n]) by { observe(v[0..n]); close(); }
    have i <= n by { close() using { i < n; }; }
    have contains(memory(v[0..n]), memory(v[0..i])) by {
        apply(click::separation::contains_subrange(v, 0, n, 0, i));
    }
    have viewable(v[0..i]) by {
        apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..i])));
    }
    step();
    have forall (k: int32) { 0 <= k and k < i implies v[k] == at(entry, v[k]) } by {
        intro(); intro();
        have i != k by { close() using { k < i; }; }
        have separate(memory(v[i]), memory(v[k])) by {
            apply(click::separation::separate_elements(v, i, k));
        }
        have separate(statement(0).footprint, memory(v[k])) by {
            close() using { separate(memory(v[i]), memory(v[k])); };
        }
        preserve(memory(v[k]), statement(0));
    }
    have viewable(v[0..n]) by { observe(v[0..n]); close(); }
    have viewable(v[0..i]) by {
        apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..i])));
    }
    have i <= 1073741823 by { close() using { i < n; n <= 1073741823; }; }
    apply(same_through(v, at(entry, v), 0, i, i));
}
```

```expect
pass
```
