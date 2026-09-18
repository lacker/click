# Reflexive orderings prove through arithmetic after locals merge

When an assignment merges two names into one variable, orderings between
them are reflexive truths. `arithmetic()` proves `i >= p` and `i <= p`
from the merged equality without further evidence.

```c filename=arithmetic_reflexive_order.c
int32 lower(int32 p) {
    int32 i;
    i = p;
    return 0;
}

int32 upper(int32 p) {
    int32 i;
    i = p;
    return 0;
}
```

```click
verifying "arithmetic_reflexive_order.c";

int32 lower(int32 p) {
    ensures result == 0;
} by {
    step();
    step();
    have i == p by {
        normalize();
    }
    have i >= p by {
        arithmetic() using {
            i == p;
        }
    }
    step();
    simp();
}

int32 upper(int32 p) {
    ensures result == 0;
} by {
    step();
    step();
    have i == p by {
        normalize();
    }
    have i <= p by {
        arithmetic() using {
            i == p;
        }
    }
    step();
    simp();
}
```

```expect
pass
```
