# A join forgets a cell the arms disagree on

The negative control for `a_join_keeps_a_cell_both_arms_agree_on`. The arms
store different values to `p->left`. The join keeps only what both arms hold
with the same value, so after it `p->left` is unknown, and the claim that the
function returns `0` is refused: it returns `1` when `x > 0`.

```c filename=a_join_forgets_a_cell_the_arms_disagree_on.c
struct pair { int32 left; int32 right; };

int32 put(struct pair *p, int32 x) {
    if (x <= 0) {
        p->left = 0;
    } else {
        p->left = 1;
    }
    return p->left;
}
```

```click
verifying "a_join_forgets_a_cell_the_arms_disagree_on.c";

int32 put(struct pair* p, int32 x) {
    requires p != 0;
    owns p->left;
    owns p->right;
    ensures result == 0;
} by {
    branch ensuring {
        fact 1 == 1;
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
fail: `ensures result == 0` failed
```
