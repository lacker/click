# a generalized induction hypothesis carries the theorem's requirements

An instantiated hypothesis states the theorem at the given parameters, so the
theorem's `requires` clauses are checked at those parameters too. Here the
proof instantiates only one side of the transport, and the requirement
`list_length(Cons(head, a)) == list_length(b)` is not available.

```click
function rev_onto(xs: List<int32>, acc: List<int32>) -> List<int32>
    decreases xs
{
    match xs {
        List::Nil => acc,
        List::Cons(head, tail) => rev_onto(tail, List<int32>::Cons(head, acc)),
    }
}

theorem rev_onto_length_transport(xs: List<int32>, a: List<int32>, b: List<int32>) {
    requires list_length(a) == list_length(b);
    ensures list_length(rev_onto(xs, a)) == list_length(rev_onto(xs, b)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(rev_onto(List<int32>::Nil, a));
                unfold(rev_onto(List<int32>::Nil, b));
                assumption();
            }
            List::Cons(head, tail) => {
                have list_length(List<int32>::Cons(head, a))
                    == list_length(List<int32>::Cons(head, b)) by {
                    unfold(list_length(List<int32>::Cons(head, a)));
                    unfold(list_length(List<int32>::Cons(head, b)));
                    rewrite(list_length(a) == list_length(b));
                    normalize();
                }
                apply(ih(tail, List<int32>::Cons(head, a), b));
                unfold(rev_onto(List<int32>::Cons(head, tail), a));
                unfold(rev_onto(List<int32>::Cons(head, tail), b));
                assumption();
            }
        }
    }
}
```

```expect
fail: induction premise is not exactly available
```
