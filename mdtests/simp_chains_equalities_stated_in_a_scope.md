# `simp` chains the equalities a scope states

Each frame across a call is one equality, so carrying a cell's value back
through two calls is a chain: `occ[k] == at(b, occ[k])`, `at(b, occ[k]) ==
at(a, occ[k])`, and `at(a, occ[k]) == 0`. `simp` closes `occ[k] == 0` from
the three in one step, rewriting along the chain.

The links are `have`s written inside the scope `intro` opened. A `have`
there used to leave no spelling for its fact, so the equality-rewrite search
found the three candidates but could cite none of them, and every link needed
its own two-premise `simp() using { .. }`. A scope's `have` is now spelled for
the premise lookups later steps of the same scope make, as one at an outcome
or an execution frontier already was. The expansion is the three `rewrite`s
and `normalize()`, and it re-verifies. The chain's work is linear in its
length and an unrelated query's is flat
(`simp_equality_chain_is_linear_and_unrelated_queries_are_flat`).

```c filename=simp_chains_equalities_stated_in_a_scope.c
void mark_one(int* other) {
    other[0] = 1;
}

int caller(int* occ, int* other, int n) {
    mark_one(other);
    mark_one(other);
    return 0;
}
```

```click
verifying "simp_chains_equalities_stated_in_a_scope.c";

void mark_one(int32* other) {
    owns other[0..1];
    ensures other[0] == 1;
} by {
    execute();
    simp();
}

int32 caller(int32* occ, int32* other, int32 n) {
    owns occ[0..n];
    owns other[0..1];
    requires 0 <= n;
    requires forall (k: int32) {
        0 <= k and k < n implies occ[k] == 0
    };
    ensures forall (k: int32) {
        0 <= k and k < n implies occ[k] == 0
    };
} by {
    mark a;
    step();
    mark b;
    step();
    have forall (k: int32) {
        0 <= k and k < n implies occ[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        have occ[k] == at(b, occ[k]) by {
            simp();
        }
        have at(b, occ[k]) == at(a, occ[k]) by {
            simp();
        }
        have at(a, occ[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and j < n implies at(a, occ[j]) == 0
            }, k) using {
                0 <= k;
                k < n;
            }
            simp();
        }
        simp();
    }
    execute();
    simp();
}
```

```expect
pass
```
