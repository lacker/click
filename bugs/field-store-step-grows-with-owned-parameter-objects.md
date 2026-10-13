# A field store's step grows with the owned parameter objects

A simple `step` over a store must cost work proportional to the store
(docs/internals/verification-efficiency.md). Storing to one field of one owned
parameter object costs work linear in how many other owned parameter objects
the function holds, so initializing N objects is quadratic.

Reproduced on master `0d2b58555` with `scripts/step-scaling-hunt.py`, which
generates the C below with an explicit one-`step()`-per-statement proof:

```c
int32 caller(int32* flags, int32* data, int32 k, struct box* b0, ..., struct box* bN) {
    int32 total;
    b0->v = 0; ... bN->v = N;          /* each store step measured */
    touch(flags, data, k);
    total = b0->v + ... + bN->v;
    return total;
}
```

```sh
python3 scripts/step-scaling-hunt.py many_objects deep_chain --sizes 1,8,32,64
```

Each `bi->v = i` step charges 63, 194, 554 and 1,034 units at N = 1, 8, 32
and 64. A pointer-valued store (`ni->next = n(i+1)`, shape `deep_chain`) grows
faster: about 5,354 units at N = 32 and 10,410 at 64. All parameters share the
`ExternalArgument` block, so an index by block does not separate them. A
profile at N = 256 shows every statement also collecting the variables of the
whole state and fact set (`statement_kernel_variables`), work that is not
charged; the charged growth is in the store's own execution and was not yet
isolated.

Diagnosis (master `b1523c784`, sampling which call paths charge the work):
the store's work is cache invalidation. `CMemory::without_possible_aliasing_cells`
asks `forget_cached_values` the fate of every cached cell its
`AliasCandidates` admit, and for an `ExternalArgument` store that is every
cached cell of every parameter object. Each one is then kept cheaply, by
ownership (`access_owned_apart_from_store`, a base-indexed lookup), but it
is still visited: about 16 units per other object. A constant store needs
the walk itself to skip cells that ownership places in another member, for
example an index from cached cells to the owned member that holds them,
consulted like the `store_gap_kept_ranges` skip.

Acceptance: a multi-size regression over the `many_objects` and `deep_chain`
shapes shows each store step's work, and its time, constant in N up to
logarithmic factors; ownership and write permission are still checked per
store; no budget or threshold is raised.
