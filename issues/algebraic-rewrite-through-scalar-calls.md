# Rewrite algebraic arguments inside scalar-valued pure calls

## Violated invariant

Exact equality must support congruence regardless of a pure call's result
type. The algebraic-equality branch in `src/surface/checking/simp.rs`
currently traverses algebraic-valued goals only. It rejects an occurrence
inside an integer-valued function application as absent.

This blocks the standard-library membership-through-append law, though
append associativity and the membership constructor equations work.

## Intended regression

With the implicit standard library, prove:

```click
theorem rewrite_append_in_contains(head: int32, tail: List<int32>,
                                  ys: List<int32>, value: int32) {
    ensures list_contains(list_append(List<int32>::Cons(head, tail), ys), value)
        == list_contains(List<int32>::Cons(head, list_append(tail, ys)), value) by {
        apply(list_append_cons(head, tail, ys));
        rewrite(list_append(List<int32>::Cons(head, tail), ys)
            == List<int32>::Cons(head, list_append(tail, ys)));
        simp();
    }
}
```

The rewrite currently reports that the equality does not occur in the goal.

## Acceptance criteria

- Check algebraic congruence through scalar-valued pure calls and conditions,
  including nested calls, without eager unfolding or unchecked substitution.
- Keep work proportional to the explicitly rewritten goal; add scaling tests
  if the traversal or certificate representation changes.
- Add negative coverage for a wrong equality and a mismatched element type.
- Verify and expand the regression using the shared checked proof engine.
- Add the generic `list_contains_append` law, proved by structural induction:
  `list_contains(list_append(xs, ys), value) == if list_contains(xs, value) == 1
  { 1 } else { list_contains(ys, value) }`.
- Run `scripts/check.sh` and remove this issue when those checks land.
