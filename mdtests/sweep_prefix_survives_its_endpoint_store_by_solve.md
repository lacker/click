# an omitted proof carries the sweep's prefix count across the endpoint store

This is `sweep_maintains_a_zero_unmarked_count.md` with its
explicit `transport(...) using { ... }` replaced by a `have` with the omitted proof. Its
state transport closure proposes the iteration-entry fact as the source and
asks the same checked transport, which reaches the checked fold read frame:
`unmarked(visited, 0, i)` reads only `visited[0..i]`, and the store writes
`visited[i]`, at the prefix's end. The fold read frame answers the same for
every caller, so no new search is involved; `click expand` rewrites this
omitted proof into that explicit transport, and the expansion re-verifies.

```c filename=sweep_prefix_survives_its_endpoint_store_by_solve.c
void sweep(int32 visited[], int32 n) {
    for (int32 i = 0; i < n; i++) {
        visited[i] = 1;
    }
}
```

```click
verifying "sweep_prefix_survives_its_endpoint_store_by_solve.c";

import "unmarked_count_lemmas.click";

void sweep(int32 visited[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    owns visited[0..n];
} by {
    step();
    step();
    have 0 <= 0;
    have unmarked(visited, 0, 0) == 0 by {
        peel(unmarked(visited, 0, 0)) using { 0 <= 0; };
        normalize();
    }
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant unmarked(visited, 0, i) == 0;
        owns visited[0..n];
        initialize by { solve(); }
        preserve by {
            mark iter;
            have i < 1073741823 by {
                solve() using { i < n; n <= 1073741823; };
            }
            have i < 2147483647 by { solve() using { i < 1073741823; }; }
            step();
            have unmarked(visited, 0, i) == 0;
            have unmarked(visited, 0, i + 1) == 0 by {
                peel(unmarked(visited, 0, i + 1)) using {
                    0 <= to_integer((i + 1) - 1);
                    to_integer((i + 1) - 1) < 2147483647;
                };
                solve();
            }
            step();
        }
    }
}
```

```expect
pass
```
