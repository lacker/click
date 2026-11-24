# A branch interface's typed call domain must hold in each arm

The join assumes the nominal domain of `is_node(r)` only because every arm
establishes it. Here the `else` arm assigns `q`, which no contract clause
types, so `is_node(r)` has no reading in that arm and the interface is
refused. The positive is
[`a_branch_interface_supplies_its_typed_call_domains_at_the_join.md`](a_branch_interface_supplies_its_typed_call_domains_at_the_join.md).

```c filename=a_branch_interface_typed_call_domain_must_hold_in_each_arm.c
struct node { int32 value; };

struct node* pick(struct node* p, struct node* q, int32 c) {
    struct node* r;
    if (c > 0) {
        r = p;
    } else {
        r = q;
    }
    return r;
}
```

```click
verifying "a_branch_interface_typed_call_domain_must_hold_in_each_arm.c";

function is_node(p: struct node*) -> int32 { 1 }

struct node* pick(struct node* p, struct node* q, int32 c) {
    requires is_node(p) == 1;
    ensures true;
} by {
    step();
    branch ensuring {
        fact is_node(r) == 1;
    } {
        true => {
            step();
        }
        false => {
            step();
        }
    }
    step();
    close();
}
```

```expect
fail: could not lower `branch ensuring` fact
```
