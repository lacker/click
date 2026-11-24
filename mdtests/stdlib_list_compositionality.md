# Lists compose through scalar calls and algebraic conditions

```click
theorem rewrite_append_in_contains(head: int32, tail: List<int32>, ys: List<int32>, value: int32) {
    ensures list::contains(list::append(List<int32>::Cons(head, tail), ys), value)
        == list::contains(List<int32>::Cons(head, list::append(tail, ys)), value) by {
        apply(list::append_cons(head, tail, ys));
        rewrite(list::append(List<int32>::Cons(head, tail), ys), List<int32>::Cons(head, list::append(tail, ys)));
        close();
    }
}

theorem nested_membership(xs: List<List<int32>>, value: List<int32>) {
    ensures list::contains(List<List<int32>>::Cons(value, xs), value) by {
        apply(list::contains_cons(value, xs, value));
        close();
    }
}

theorem nested_append(xs: List<List<int32>>, ys: List<List<int32>>, value: List<int32>) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        apply(list::contains_append(xs, ys, value));
    }
}

theorem scalar_append(xs: List<int32>, ys: List<int32>, value: int32) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        apply(list::contains_append(xs, ys, value));
    }
}

function adt_equal<T>(xs: List<T>, ys: List<T>) -> int32 {
    if xs == ys { 1 } else { 0 }
}

theorem symbolic_comparison(xs: List<int32>, ys: List<int32>) {
    ensures adt_equal(xs, ys) == if xs == ys { 1 } else { 0 } by {
        unfold(adt_equal(xs, ys));
        close();
    }
}

theorem rewrite_inside_condition(xs: List<int32>, ys: List<int32>, zs: List<int32>) {
    requires xs == ys;
    ensures (if xs == zs { 1 } else { 0 }) == (if ys == zs { 1 } else { 0 }) by {
        rewrite(xs, ys);
        close();
    }
    ensures adt_equal(list::append(xs, zs), zs) == adt_equal(list::append(ys, zs), zs) by {
        rewrite(xs, ys);
        close();
    }
}

theorem known_distinct(xs: List<List<int32>>, value: int32) {
    ensures list::contains(List<List<int32>>::Cons(List<int32>::Cons(value, List<int32>::Nil), xs), List<int32>::Nil)
        == list::contains(xs, List<int32>::Nil) by {
        apply(list::contains_cons(List<int32>::Cons(value, List<int32>::Nil), xs, List<int32>::Nil));
        close();
    }
}

theorem pointer_append(xs: List<int32*>, ys: List<int32*>, value: int32*) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        apply(list::contains_append(xs, ys, value));
    }
}
```

```expect
pass
```
