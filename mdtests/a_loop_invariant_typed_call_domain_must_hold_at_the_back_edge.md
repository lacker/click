# A loop invariant's typed call domain must hold at the back edge

The head assumes the nominal domain of `is_node(p)` only because entry and
every back edge must establish it. Here the back edge assigns `q`, which no
contract clause types, so the reassigned `p` has no evidence of class
`struct node` and the invariant cannot hold there. The positive is
[`a_loop_invariant_supplies_its_typed_call_domains_at_the_head.md`](a_loop_invariant_supplies_its_typed_call_domains_at_the_head.md).

```c filename=a_loop_invariant_typed_call_domain_must_hold_at_the_back_edge.c
struct node { int32 value; };

struct node* settle(struct node* p, struct node* q, int32 n) {
    while (n > 0) {
        p = q;
        n = n - 1;
    }
    return p;
}
```

```click
verifying "a_loop_invariant_typed_call_domain_must_hold_at_the_back_edge.c";

function is_node(p: struct node*) -> int32 { 1 }

struct node* settle(struct node* p, struct node* q, int32 n) {
    requires is_node(p) == 1;
    ensures true;
} by {
    loop {
        decreases n;
        invariant is_node(p) == 1;
        initialize by close();
        maintain by { step(); step(); }
    }
}
```

```expect
fail: closure body did not prove every invariant obligation
```
