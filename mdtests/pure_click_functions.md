# pure Click functions can be used in predicates and postconditions

This checks the first pure-function slice: `.click` can define expression-bodied
value functions with `->`, call them from propositions and predicates, and use
`old(function(...))` to evaluate the same definition against entry memory.

```c filename=pure_click_functions.c
int32 increment_value(int32 x) {
    return x + 1;
}
```

```c filename=read_first_with_function.c
int32 read_first_with_function(int32 p[1]) {
    return p[0];
}
```

```c filename=branch_indicator.c
int32 branch_indicator(int32 x, int32 y) {
    if (x == y) {
        return 1;
    } else {
        return 0;
    }
}
```

```click
verifying "pure_click_functions.c";
verifying "read_first_with_function.c";
verifying "branch_indicator.c";

function inc(int32 x) -> int32 {
    x + 1
}

function head(int32 p[]) -> int32 {
    p[0]
}

function eq_as_int(int32 x, int32 y) -> int32 {
    if x == y { 1 } else { 0 }
}

predicate one_more(int32 x, int32 y) {
    inc(x) == y
}

int32 increment_value(int32 x) {
    requires x < 2147483647;
    ensures result_value: result == inc(x) by simp;
    ensures predicate_value: one_more(x, result) by {
        symbolic_execute();
        unfold(one_more);
        simp();
        close();
    }
}

int32 read_first_with_function(int32 p[1]) {
    requires valid_range(p[0..1]);
    ensures current_value: result == head(p) by auto;
    ensures old_value: result == old(head(p)) by auto;
}

int32 branch_indicator(int32 x, int32 y) {
    ensures result_value: result == eq_as_int(x, y) by auto;
}
```

```expect
pass
```
