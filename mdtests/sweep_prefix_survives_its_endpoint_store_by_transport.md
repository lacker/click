# the sweep's prefix count survives the endpoint store by explicit transport

This is the C of `sweep_maintains_a_zero_unmarked_count.md`, unchanged. There
the invariant `unmarked(visited, 0, i) == 0` is carried across
`visited[i] = 1` by the imported `unmarked_frame` lemma plus a quantified
per-cell transport. Here one explicit `transport` carries it.

`unmarked` has a checked read summary: its body is a top-level `int32` range
fold that reads `v` only at its own binder, so an application reads exactly
the cells `v + 4*k` for `lo <= k < hi`. The store writes the four bytes at
`visited + 4*i`, which start at the prefix's end, so the kernel frames the
application across it. The following increment of `i` still needs the fold's
append law, which the proof keeps.

```c filename=sweep_prefix_survives_its_endpoint_store_by_transport.c
void sweep(int32 visited[], int32 n) {
    for (int32 i = 0; i < n; i++) {
        visited[i] = 1;
    }
}
```

```click
verifying "sweep_prefix_survives_its_endpoint_store_by_transport.c";

import "unmarked_count_lemmas.click";

void sweep(int32 visited[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    consumes visited[0..n];
    produces visited[0..n];
} by {
    step();
    step();
    have 0 <= 0 by { simp(); }
    have unmarked(visited, 0, 0) == 0 by {
        unfold(unmarked(visited, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant unmarked(visited, 0, i) == 0;
        owns visited[0..n];
        initialize by { simp(); }
        preserve by {
            mark iter;
            have i < 1073741823 by {
                arithmetic() using { i < n; n <= 1073741823; }
            }
            have i < 2147483647 by { arithmetic() using { i < 1073741823; } }
            step();
            have unmarked(visited, 0, i) == 0 by {
                transport(
                    at(iter, unmarked(visited, 0, i)) == 0,
                    unmarked(visited, 0, i) == 0
                ) using {
                    at(iter, unmarked(visited, 0, i)) == 0;
                }
                assumption();
            }
            have unmarked(visited, 0, i + 1) == 0 by {
                unfold(unmarked(visited, 0, i + 1)) using {
                    0 <= (i + 1) - 1;
                    (i + 1) - 1 < 2147483647;
                }
                simp();
            }
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
