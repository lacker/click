# A known list position still closes through unfolding

```click quick-solve
function adjacent(xs: List<int32>, first: int32, second: int32) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) =>
            if head == first {
                match tail {
                    List::Nil => 0,
                    List::Cons(next, rest) => if next == second { 1 } else { 0 },
                }
            } else {
                adjacent(tail, first, second)
            },
    }
}

theorem right_position(xs: List<int32>, tail: List<int32>, first: int32, second: int32, flag: int32) {
    requires xs == List<int32>::Cons(first, List<int32>::Cons(second, tail));
    ensures flag != 0 implies adjacent(xs, first, second) == 1 by {
        close();
    }
}
```

```expect
pass
```
