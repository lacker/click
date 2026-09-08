# Distinct constructors do not become equal in a conditional

```click
theorem false_member() {
    ensures list_contains(List<List<int32>>::Cons(List<int32>::Nil, List<List<int32>>::Nil),
                          List<int32>::Cons(1, List<int32>::Nil)) == 1 by {
        unfold(list_contains(List<List<int32>>::Cons(List<int32>::Nil, List<List<int32>>::Nil),
                             List<int32>::Cons(1, List<int32>::Nil)));
        unfold(list_contains(List<List<int32>>::Nil, List<int32>::Cons(1, List<int32>::Nil)));
        simp();
    }
}
```

```expect
fail: simp
```
