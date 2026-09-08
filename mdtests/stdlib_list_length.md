# stdlib list length

```click
theorem length_laws<T>(head: T, xs: List<T>, ys: List<T>) {
    ensures list_length(List<T>::Nil) == Nat::Zero by {
        apply(list_length_nil(List<T>::Nil));
    }
    ensures list_length(List<T>::Cons(head, xs)) == Nat::Succ(list_length(xs)) by {
        apply(list_length_cons(head, xs));
    }
    ensures list_length(list_append(xs, ys)) == nat_add(list_length(xs), list_length(ys)) by {
        apply(list_length_append(xs, ys));
    }
}

theorem nested_length(xs: List<List<int32>>, ys: List<List<int32>>) {
    ensures list_length(list_append(xs, ys)) == nat_add(list_length(xs), list_length(ys)) by {
        apply(list_length_append(xs, ys));
    }
}

theorem singleton_length(value: int32) {
    ensures list_length(List<int32>::Cons(value, List<int32>::Nil)) == Nat::Succ(Nat::Zero) by {
        unfold(list_length(List<int32>::Cons(value, List<int32>::Nil)));
        unfold(list_length(List<int32>::Nil));
        simp();
    }
}
```

```expect
pass
```
