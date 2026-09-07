# generic theorems are checked at concrete applications

Generic theorem parameters use the same Rust-like syntax and call-site type
inference as logical functions. Each concrete instance is checked before an
`apply` step may use its conclusion. This example exercises structural
induction and two distinct element types.

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

spec enum Maybe<T> {
    None,
    Some(T),
}

function append<T>(xs: TestList<T>, ys: TestList<T>) -> TestList<T>
    decreases xs
{
    match xs {
        TestList::Nil => ys,
        TestList::Cons(head, tail) => TestList<T>::Cons(head, append(tail, ys)),
    }
}

theorem append_right_identity<T>(xs: TestList<T>) {
    ensures append(xs, TestList<T>::Nil) == xs by {
        induct(xs) as ih {
            TestList::Nil => {
                unfold(append(TestList<T>::Nil, TestList<T>::Nil));
                simp();
            }
            TestList::Cons(head, tail) => {
                apply(ih(tail));
                unfold(append(TestList<T>::Cons(head, tail), TestList<T>::Nil));
                rewrite(append(tail, TestList<T>::Nil) == tail);
                normalize();
            }
        }
    }
}

theorem reflexive<T>(value: T) {
    ensures value == value by simp;
}

theorem reflexive_via_generic<T>(value: T) {
    ensures value == value by {
        apply(reflexive(value));
        assumption();
    }
}

theorem retain<T>(left: T, right: T) {
    requires left == right;
    ensures left == right by {
        assumption();
    }
}

theorem int32_instance(xs: TestList<int32>) {
    ensures append(xs, TestList<int32>::Nil) == xs by {
        apply(append_right_identity(xs));
        assumption();
    }
}

theorem pointer_instance(xs: TestList<int32*>) {
    ensures append(xs, TestList<int32*>::Nil) == xs by {
        apply(append_right_identity(xs));
        assumption();
    }
}

theorem scalar_parameter_instance(value: int32) {
    requires value == value;
    ensures value == value by {
        apply(retain(value, value)) using { value == value; }
        apply(reflexive_via_generic(value));
        assumption();
    }
}

theorem generic_requirement_instance(left: int32, right: int32) {
    requires left == right;
    ensures left == right by {
        apply(retain(left, right));
        assumption();
    }
}

theorem pointer_parameter_instance(value: int32*) {
    ensures value == value by {
        apply(reflexive_via_generic(value));
        assumption();
    }
}

theorem algebraic_parameter_instance(value: Maybe<int32>) {
    ensures value == value by {
        apply(reflexive_via_generic(value));
        assumption();
    }
}
```

```expect
pass
```
