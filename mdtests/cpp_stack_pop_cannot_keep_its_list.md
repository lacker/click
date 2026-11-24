# The C++ stack's pop cannot claim it keeps its list

`Stack<int>::pop` removes the front node, so its list afterwards is the rest
of the list it started with. A contract claiming the list is unchanged is
refused (`examples/cpp-stack/` verifies the true one).

```cpp filename=stack.cpp function=round_trip profile=normal_only
template<class T> struct Node {
    T value;
    Node* next;
};

template<class T> class Stack {
    Node<T>* head = nullptr;
    unsigned long count = 0;

public:
    void push(T value) noexcept {
        head = new Node<T>{value, head};
        count = count + 1;
    }

    bool pop(T& out) noexcept {
        if (head == nullptr) {
            return false;
        }
        Node<T>* node = head;
        out = node->value;
        head = node->next;
        delete node;
        count = count - 1;
        return true;
    }

    unsigned long size() const noexcept { return count; }
};

int round_trip(int x) noexcept {
    Stack<int> stack;
    stack.push(x);
    int out = 0;
    stack.pop(out);
    return out;
}
```

```click
import click::integer;
verifying "stack.cpp";

resource nodes(p: Node<int>*) {
    field items: List<int32>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns allocation(p, sizeof(Node<int>));
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

function first_or(xs: List<int32>, fallback: int32) -> int32 {
    match xs {
        List::Nil => fallback,
        List::Cons(value, rest) => value,
    }
}

function is_cons(xs: List<int32>) -> Bool {
    match xs {
        List::Nil => false,
        List::Cons(value, rest) => true,
    }
}

function rest(xs: List<int32>) -> List<int32> {
    match xs {
        List::Nil => List<int32>::Nil,
        List::Cons(value, tail) => tail,
    }
}

void Stack<int>::push(int value) {
    owns *this;
    consumes before: nodes(this->head);
    produces after: nodes(this->head);
    requires length(before.items) < 1000000;
    requires to_integer(this->count) == length(before.items);
    ensures after.items == List::Cons(value, old(before.items));
    ensures to_integer(this->count) == length(after.items);
} by {
    step_until(function.exit);
    let after = fold(nodes(this->head), { items: List::Cons(value, old(before.items)), tail: before });
    unfold(length(List::Cons(value, old(before.items))));
    have to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
    have to_integer(old(this->count) + 1u64) == length(List::Cons(value, old(before.items))) by close() using {
        to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
        to_integer(old(this->count)) == length(old(before.items));
        length(List::Cons(value, old(before.items))) == length(old(before.items)) + 1;
    };
    close();
}

bool Stack<int>::pop(int& out) {
    owns *this;
    owns out;
    consumes before: nodes(this->head);
    produces after: nodes(this->head);
    requires to_integer(this->count) == length(before.items);
    ensures result == is_cons(old(before.items));
    ensures out == first_or(old(before.items), old(out));
    ensures after.items == old(before.items);
    ensures to_integer(this->count) == length(after.items);
} by {
    match before.items {
        List::Nil => {
            unfold(before);
            step_until(function.exit);
            let after = fold(nodes(this->head), { items: List<int32>::Nil });
            unfold(length(List<int32>::Nil));
            unfold(is_cons(List<int32>::Nil));
            unfold(first_or(List<int32>::Nil, old(out)));
            unfold(rest(List<int32>::Nil));
        },
        List::Cons(value, tail_items) => {
            let { tail: tail } = unfold(before);
            unfold(length(List::Cons(value, tail_items)));
            apply(length_nonnegative(tail_items));
            step_until(function.exit);
            unfold(is_cons(List::Cons(value, tail_items)));
            unfold(first_or(List::Cons(value, tail_items), old(out)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let after = fold(nodes(this->head), { items: List<int32>::Nil });
                    unfold(length(List<int32>::Nil));
                    have length(tail_items) == 0 by close();
                    have to_integer(old(this->count)) == 1 by close() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                        length(tail_items) == 0;
                    };
                    close();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let after = fold(nodes(this->head), { items: List::Cons(next_value, next_items), tail: next });
                    have to_integer(old(this->count)) == length(tail_items) + 1 by close() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                    };
                    have to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                    have to_integer(old(this->count) - 1u64) == length(tail_items) by close() using {
                        to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                        to_integer(old(this->count)) == length(tail_items) + 1;
                    };
                    close();
                },
            }
        },
    }
}
```

```expect
fail: `ensures after.items == old(before.items)` failed
```
