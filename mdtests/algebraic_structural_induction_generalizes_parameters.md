# structural induction generalizes the theorem's other parameters

An accumulating recursion reaches its recursive call with a different second
argument, so the induction hypothesis has to be available at that argument
too. Spelling the complete parameter list instantiates every position: the
inducted one must name a field this arm bound, and the others may name any
well-typed term. This arm uses two instances of the same hypothesis, at
`Cons(head, acc)` and at `Cons(head, Nil)`.

```click
function rev_onto(xs: List<int32>, acc: List<int32>) -> List<int32>
    decreases xs
{
    match xs {
        List::Nil => acc,
        List::Cons(head, tail) => rev_onto(tail, List<int32>::Cons(head, acc)),
    }
}

theorem rev_onto_appends(xs: List<int32>, acc: List<int32>) {
    ensures rev_onto(xs, acc) == list_append(rev_onto(xs, List<int32>::Nil), acc) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(rev_onto(List<int32>::Nil, acc));
                unfold(rev_onto(List<int32>::Nil, List<int32>::Nil));
                apply(list_append_left_identity(acc));
                rewrite(list_append(List<int32>::Nil, acc) == acc);
                normalize();
            }
            List::Cons(head, tail) => {
                apply(ih(tail, List<int32>::Cons(head, acc)));
                apply(ih(tail, List<int32>::Cons(head, List<int32>::Nil)));
                apply(list_append_associative(rev_onto(tail, List<int32>::Nil),
                    List<int32>::Cons(head, List<int32>::Nil), acc));
                apply(list_append_cons(head, List<int32>::Nil, acc));
                apply(list_append_left_identity(acc));
                unfold(rev_onto(List<int32>::Cons(head, tail), acc));
                unfold(rev_onto(List<int32>::Cons(head, tail), List<int32>::Nil));
                rewrite(rev_onto(tail, List<int32>::Cons(head, List<int32>::Nil))
                    == list_append(rev_onto(tail, List<int32>::Nil),
                        List<int32>::Cons(head, List<int32>::Nil)));
                rewrite(list_append(list_append(rev_onto(tail, List<int32>::Nil),
                        List<int32>::Cons(head, List<int32>::Nil)), acc)
                    == list_append(rev_onto(tail, List<int32>::Nil),
                        list_append(List<int32>::Cons(head, List<int32>::Nil), acc)));
                rewrite(list_append(List<int32>::Cons(head, List<int32>::Nil), acc)
                    == List<int32>::Cons(head, list_append(List<int32>::Nil, acc)));
                rewrite(list_append(List<int32>::Nil, acc) == acc);
                rewrite(rev_onto(tail, List<int32>::Cons(head, acc))
                    == list_append(rev_onto(tail, List<int32>::Nil),
                        List<int32>::Cons(head, acc)));
                normalize();
            }
        }
    }
}
```

```expect
pass
```
