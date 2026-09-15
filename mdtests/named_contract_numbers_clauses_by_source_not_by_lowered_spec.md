# A named contract's refused clause is numbered by the clause it wrote

The named-contract form of
`contract_numbers_clauses_by_source_not_by_lowered_spec.md`. The embedded
struct array field `owns n->payload;` lowers to two specs, and the stalled
clause after it is still the second of two clauses: the surface check that
spells the segment as written and the kernel evaluator behind it agree on
the source numbering.

```c filename=bump.c
struct pair {
    int32 first;
    int32 second;
};

struct node {
    struct pair payload[2];
    struct node *next;
    int32 augmented;
};

void bump(struct node *n) { n->augmented = n->next->augmented; }
```

```click
verifying "bump.c";

contract void Bump(struct node* n) {
    requires n != 0;
    owns n->payload;
    views n->next->augmented;
}
```

```expect
fail: could not address resource clause `n->next->augmented` (resource clause 2 of 2)
```
