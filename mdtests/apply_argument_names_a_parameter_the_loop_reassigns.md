# A theorem argument naming a parameter the loop reassigns is read where the tactic stands

`skip` reassigns its pointer parameter `p` in a loop. Inside `preserve`, before
any statement of the body has run, the proof states a fact about `p` with a
`have` and then applies a theorem to `p`, citing that fact as the theorem's
premise.

The application used to be refused: the premise was reported unavailable
although the `have` immediately above it had recorded exactly that proposition.
The theorem's requirement instantiated to
`holds(Box::Box(p), array-ref(state#1, p))`: the occurrence of `p` inside
the constructor was the loop head's value, and the occurrence passed directly
as a pointer argument was read at function entry. A pointer parameter has two
entries in a proof-side environment, its value and the array reference a
pointer-typed pure-function or theorem parameter binds, and only the value
followed the variable once the body assigned it. The two now agree: the
reference is read through the variable, like the value.

With the assignment `p = q` removed from the C body the proof always verified,
and `old(p)` still names the entry pointer. The unchanged Linux `rb_next`
reassigns its `node` parameter in both walks and applies theorems to it in each.

The logical pointer annotations below use `void*` for address identities;
object access remains governed by the unchanged C types and resource ownership.

```c filename=skip.c
struct node { int32 value; };

struct node *skip(struct node *p, struct node *q, int32 n) {
    while (n > 0) {
        p = q;
        n = n - 1;
    }
    return p;
}
```

```click
verifying "skip.c";

spec enum Box { Box(void*) }

function holds(b: Box, p: void*) -> int32 {
    match b {
        Box::Box(q) => if q == p { 1 } else { 0 },
    }
}

theorem holds_is_nonzero(p: void*) {
    requires holds(Box::Box(p), p) == 1;
    ensures holds(Box::Box(p), p) != 0 by {
        rewrite(holds(Box::Box(p), p), 1);
        normalize();
    }
}

struct node* skip(struct node* p, struct node* q, int32 n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;

        initialize by solve();
        preserve by {
            have holds(Box::Box(p), p) == 1 by {
                unfold(holds(Box::Box(p), p));
                normalize();
            }
            have holds(Box::Box(p), p) != 0 by {
                apply(holds_is_nonzero(p)) using {
                    holds(Box::Box(p), p) == 1;
                };
                known();
            }
            step();
            step();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
