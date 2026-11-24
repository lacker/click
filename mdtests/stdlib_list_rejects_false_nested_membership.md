# Distinct constructors do not become equal in a conditional

```click
theorem false_member() {
    ensures list::contains(List<List<int32>>::Cons(List<int32>::Nil, List<List<int32>>::Nil),
                          List<int32>::Cons(1, List<int32>::Nil)) == true by {
        unfold(list::contains(List<List<int32>>::Cons(List<int32>::Nil, List<List<int32>>::Nil),
                             List<int32>::Cons(1, List<int32>::Nil)));
        unfold(list::contains(List<List<int32>>::Nil, List<int32>::Cons(1, List<int32>::Nil)));
        close();
    }
}
```

```expect
fail: solve
```
