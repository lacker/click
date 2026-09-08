# Lists compose through scalar calls and algebraic conditions

```click
theorem rewrite_append_in_contains(head: int32, tail: List<int32>, ys: List<int32>, value: int32) {
    ensures list_contains(list_append(List<int32>::Cons(head, tail), ys), value)
        == list_contains(List<int32>::Cons(head, list_append(tail, ys)), value) by {
        apply(list_append_cons(head, tail, ys));
        rewrite(list_append(List<int32>::Cons(head, tail), ys)
            == List<int32>::Cons(head, list_append(tail, ys)));
        simp();
    }
}

theorem nested_membership(xs: List<List<int32>>, value: List<int32>) {
    ensures list_contains(List<List<int32>>::Cons(value, xs), value) == 1 by {
        apply(list_contains_cons(value, xs, value));
        simp();
    }
}

theorem nested_append(xs: List<List<int32>>, ys: List<List<int32>>, value: List<int32>) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) == 1 { 1 } else { list_contains(ys, value) } by {
        apply(list_contains_append(xs, ys, value));
    }
}

theorem scalar_append(xs: List<int32>, ys: List<int32>, value: int32) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) == 1 { 1 } else { list_contains(ys, value) } by {
        apply(list_contains_append(xs, ys, value));
    }
}

function adt_equal<T>(xs: List<T>, ys: List<T>) -> int32 {
    if xs == ys { 1 } else { 0 }
}

theorem symbolic_comparison(xs: List<int32>, ys: List<int32>) {
    ensures adt_equal(xs, ys) == if xs == ys { 1 } else { 0 } by {
        unfold(adt_equal(xs, ys));
        normalize();
    }
}

theorem rewrite_inside_condition(xs: List<int32>, ys: List<int32>, zs: List<int32>) {
    requires xs == ys;
    ensures (if xs == zs { 1 } else { 0 }) == (if ys == zs { 1 } else { 0 }) by {
        rewrite(xs == ys);
        normalize();
    }
    ensures adt_equal(list_append(xs, zs), zs) == adt_equal(list_append(ys, zs), zs) by {
        rewrite(xs == ys);
        normalize();
    }
}

theorem known_distinct(xs: List<List<int32>>, value: int32) {
    ensures list_contains(List<List<int32>>::Cons(List<int32>::Cons(value, List<int32>::Nil), xs), List<int32>::Nil)
        == list_contains(xs, List<int32>::Nil) by {
        apply(list_contains_cons(List<int32>::Cons(value, List<int32>::Nil), xs, List<int32>::Nil));
        simp();
    }
}

theorem pointer_append(xs: List<int32*>, ys: List<int32*>, value: int32*) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) == 1 { 1 } else { list_contains(ys, value) } by {
        apply(list_contains_append(xs, ys, value));
    }
}
```

```expect
pass
```
