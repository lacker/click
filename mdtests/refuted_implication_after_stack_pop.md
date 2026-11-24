# A matched nonempty list promptly refutes the empty-list postcondition

The original stack-pop program and proof retain their empty-list implication
after mutation, deallocation, and refolding. Its constructor premise is
spelled at function entry without reconstructing unrelated memory history.

```c filename=pop.c
struct node { int value; struct node *next; };
struct stack { struct node *head; unsigned long count; };
_Bool pop(struct stack *s, int *out) {
    if (s->head == 0) {
        return 0;
    }
    struct node *node = s->head;
    *out = node->value;
    s->head = node->next;
    free(node);
    s->count = s->count - 1;
    return 1;
}
```

```click
import click::integer;
verifying "pop.c";

resource nodes(p: struct node*) {
    field items: List<int32>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns allocation(p, sizeof(struct node));
            owns *p;
            owns tail: nodes(p->next);
            fact p != 0;
            fact aligned(p, 8);
            fact p->value == value;
            fact tail.items == rest;
        },
    }
}

function length(xs: List<int32>) -> Integer
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(value, rest) => length(rest) + 1,
    }
}

theorem length_nonnegative(xs: List<int32>) {
    ensures length(xs) >= 0 by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(length(List<int32>::Nil));
                close();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<int32>::Cons(value, rest)));
                close() using { length(rest) >= 0; };
            }
        }
    }
}

function first(xs: List<int32>) -> int32 {
    match xs {
        List::Nil => 0,
        List::Cons(value, rest) => value,
    }
}

function rest(xs: List<int32>) -> List<int32> {
    match xs {
        List::Nil => List<int32>::Nil,
        List::Cons(value, tail) => tail,
    }
}

bool pop(struct stack* s, int32* out) {
    owns *s;
    owns *out;
    consumes before: nodes(s->head);
    produces after: nodes(s->head);
    requires to_integer(s->count) == length(before.items);
    ensures old(before.items) == List<int32>::Nil implies result == false;
    ensures to_integer(s->count) == length(after.items);
} by {
    match before.items {
        List::Nil => {
            unfold(before);
            step_until(function.exit);
            let after = fold(nodes(s->head), { items: List<int32>::Nil });
            unfold(length(List<int32>::Nil));
        },
        List::Cons(value, tail_items) => {
            let { tail: tail } = unfold(before);
            unfold(length(List::Cons(value, tail_items)));
            apply(length_nonnegative(tail_items));
            step_until(function.exit);
            unfold(first(List::Cons(value, tail_items)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let after = fold(nodes(s->head), { items: List<int32>::Nil });
                    unfold(length(List<int32>::Nil));
                    have length(tail_items) == 0 by close();
                    have to_integer(old(s->count)) == 1 by close() using {
                        to_integer(old(s->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                        length(tail_items) == 0;
                    };
                    close();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let after = fold(nodes(s->head), { items: List::Cons(next_value, next_items), tail: next });
                    have to_integer(old(s->count)) == length(tail_items) + 1 by close() using {
                        to_integer(old(s->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                    };
                    have to_integer(old(s->count) - 1u64) == to_integer(old(s->count)) - to_integer(1u64);
                    have to_integer(old(s->count) - 1u64) == length(tail_items) by close() using {
                        to_integer(old(s->count) - 1u64) == to_integer(old(s->count)) - to_integer(1u64);
                        to_integer(old(s->count)) == length(tail_items) + 1;
                    };
                    close();
                },
            }
        },
    }
}
```

```expect
pass
```
