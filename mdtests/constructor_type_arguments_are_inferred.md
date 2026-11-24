# Constructor type arguments are inferred

A constructor of a generic datatype may leave out its type arguments when its
own arguments or its position fix them: `List::Cons(x, List::Nil)` takes `T`
from `x`, and the inner `List::Nil` from the field it fills; a function's
result, a call's parameter and the other side of a comparison fix the rest.
The written form `List<int32>::Nil` is still accepted, and the kernel sees the
same fully applied constructor either way.

```click
function singleton(x: int32) -> List<int32> {
    List::Cons(x, List::Nil)
}

function nothing() -> List<int32> {
    List::Nil
}

function rest(xs: List<int32>) -> List<int32> {
    match xs {
        List::Nil => List::Nil,
        List::Cons(head, tail) => List::Cons(head, List::Nil),
    }
}

theorem singleton_is_one_cons(x: int32) {
    ensures singleton(x) == List::Cons(x, List<int32>::Nil) by {
        unfold(singleton(x));
        close();
    }
}

theorem append_nothing(xs: List<int32>) {
    ensures list::append(List::Nil, xs) == xs by {
        unfold(list::append(List::Nil, xs));
        close();
    }
}

theorem singleton_contains(x: int32) {
    ensures list::contains(List::Cons(x, List::Nil), x) by {
        unfold(list::contains(List::Cons(x, List::Nil), x));
        close();
    }
}
```

```expect
pass
```
