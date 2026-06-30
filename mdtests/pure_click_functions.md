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

```c filename=count_three_matches.c
int32 count_three_matches(int32 p[3], int32 x) {
    int32 count;
    count = 0;
    if (p[0] == x) {
        count = count + 1;
    } else {
        count = count;
    }
    if (p[1] == x) {
        count = count + 1;
    } else {
        count = count;
    }
    if (p[2] == x) {
        count = count + 1;
    } else {
        count = count;
    }
    return count;
}
```

```c filename=range_helpers.c
int32 range_helpers() {
    return 0;
}
```

```c filename=identity_permutation.c
int32 identity_permutation(int32 p[3]) {
    return 0;
}
```

```click
verifying "pure_click_functions.c";
verifying "read_first_with_function.c";
verifying "branch_indicator.c";
verifying "count_three_matches.c";
verifying "range_helpers.c";
verifying "identity_permutation.c";

function inc(int32 x) -> int32 {
    x + 1
}

function head(int32 p[]) -> int32 {
    p[0]
}

function eq_as_int(int32 x, int32 y) -> int32 {
    if x == y { 1 } else { 0 }
}

function count3(int32 p[], int32 x) -> int32 {
    let initial = 0;
    (0..3).fold(initial, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
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
    requires read(p[0..1]);
    ensures current_value: result == head(p) by auto;
    ensures old_value: result == old(head(p)) by auto;
}

int32 branch_indicator(int32 x, int32 y) {
    ensures result_value: result == eq_as_int(x, y) by auto;
}

int32 count_three_matches(int32 p[3], int32 x) {
    requires valid_range(p[0..3]);
    requires read(p[0..3]);
    ensures result_value: result == count3(p, x) by auto;
    ensures stdlib_count_value: result == count(p, 0, 3, x) by auto;
}

int32 range_helpers() {
    ensures all_reflexive: (0..3).all(|k| { k == k }) by {
        symbolic_execute();
        simp();
        close();
    }
    ensures any_has_one: (0..3).any(|k| { k == 1 }) by {
        symbolic_execute();
        simp();
        close();
    }
}

int32 identity_permutation(int32 p[3]) {
    requires valid_range(p[0..3]);
    ensures same_multiset: permutation(p, p, 0, 3) by {
        symbolic_execute();
        unfold(permutation);
        simp();
        close();
    }
}
```

```expect
pass
```
