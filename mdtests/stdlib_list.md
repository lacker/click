# Implicit standard-library lists

The library defines the datatype, operations, and generic proofs. This client
only applies them; it does not redeclare them.

```click
theorem list_laws(xs: List<int32>, ys: List<int32>, zs: List<int32>, value: int32) {
    ensures list_append(List<int32>::Nil, xs) == xs by {
        apply(list_append_left_identity(xs));
        assumption();
    }
    ensures list_append(xs, List<int32>::Nil) == xs by {
        apply(list_append_right_identity(xs));
        assumption();
    }
    ensures list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs)) by {
        apply(list_append_associative(xs, ys, zs));
        assumption();
    }
    ensures list_contains(List<int32>::Nil, value) == 0 by {
        apply(list_contains_nil(value));
        assumption();
    }
    ensures list_contains(List<int32>::Cons(value, xs), value) == 1 by {
        apply(list_contains_cons(value, xs, value));
        simp();
    }
}

theorem pointer_lists(xs: List<int32*>, ys: List<int32*>, zs: List<int32*>, value: int32*) {
    ensures list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs)) by {
        apply(list_append_associative(xs, ys, zs));
        assumption();
    }
}

theorem explicit_induction_application(xs: List<int32>) {
    ensures list_append(xs, List<int32>::Nil) == xs by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<int32>::Nil, List<int32>::Nil));
                normalize();
            }
            List::Cons(head, tail) => {
                apply(list_append_right_identity(tail)) using { }
                unfold(list_append(List<int32>::Cons(head, tail), List<int32>::Nil));
                rewrite(list_append(tail, List<int32>::Nil) == tail);
                normalize();
            }
        }
    }
}

theorem nested_lists(xs: List<List<int32>>) {
    ensures list_append(xs, List<List<int32>>::Nil) == xs by {
        apply(list_append_right_identity(xs));
        assumption();
    }
}
```

```expect
pass
```
