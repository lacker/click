# generic pure functions and predicates over algebraic datatypes

Logical declarations use Rust-like type parameters. Call sites infer concrete
arguments from their values, while constructors continue to state their
concrete datatype application explicitly.

```c filename=algebraic_generic_functions.c
int32 passthrough(int32 value) {
    return value;
}
```

```click
verifying "algebraic_generic_functions.c";

spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

function list_length<T>(xs: TestList<T>) -> int32
    decreases xs
{
    match xs {
        TestList::Nil => 0,
        TestList::Cons(head, tail) => 1 + list_length(tail),
    }
}

function append<T>(xs: TestList<T>, ys: TestList<T>) -> TestList<T>
    decreases xs
{
    match xs {
        TestList::Nil => ys,
        TestList::Cons(head, tail) => TestList<T>::Cons(head, append(tail, ys)),
    }
}

function identity<T>(value: T) -> T {
    value
}

function head_or<T>(xs: TestList<T>, fallback: T) -> T {
    match xs {
        TestList::Nil => fallback,
        TestList::Cons(head, tail) => head,
    }
}

predicate is_empty<T>(xs: TestList<T>) {
    xs == TestList<T>::Nil
}

predicate same<T>(left: T, right: T) {
    left == right
}

theorem generic_list_instances(
    value: int32,
    tail: TestList<int32>,
    ys: TestList<int32>
) {
    ensures list_length(TestList<int32>::Nil) == 0 by {
        unfold(list_length(TestList<int32>::Nil));
        simp();
    }
    ensures append(TestList<int32>::Cons(value, tail), ys)
        == TestList<int32>::Cons(value, append(tail, ys)) by {
        unfold(append(TestList<int32>::Cons(value, tail), ys));
        simp();
    }
    ensures is_empty(TestList<int32>::Nil) by {
        unfold(is_empty);
        simp();
    }
    ensures identity(7) == 7 by {
        unfold(identity(7));
        simp();
    }
    ensures head_or(TestList<int32>::Cons(value, tail), 0) == value by {
        unfold(head_or(TestList<int32>::Cons(value, tail), 0));
        simp();
    }
    ensures same(value, value) by {
        unfold(same);
        simp();
    }
}

int32 passthrough(int32 value) {
    ensures result == identity(value);
} by {
    unfold(identity(value));
    step();
    simp();
}
```

```expect
pass
```
