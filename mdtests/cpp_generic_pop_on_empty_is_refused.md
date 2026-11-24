# A generic pop cannot claim a value from an empty stack

`Stack<T>::pop`, proved once for every type over the generic resource
`nodes<T>`, returns `false` on an empty list. A contract claiming it always
returns `true` is refused at the abstract type, in the empty case, while the
rest of its proof checks (`cpp_generic_resource_checked_once.md` proves the
true one).

```cpp filename=stack.cpp function=round_trip;pushed_size profile=normal_only templates=Stack<T>
template<class T> struct Node {
    T value;
    Node* next;
};

template<class T> class Stack {
    Node<T>* head = nullptr;
    unsigned long count = 0;

public:
    ~Stack() noexcept {
        while (head != nullptr) {
            Node<T>* node = head;
            head = node->next;
            delete node;
        }
    }

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

unsigned long pushed_size(int x) noexcept {
    Stack<int> stack;
    stack.push(x);
    stack.push(x);
    return stack.size();
}
```

```click
import click::integer;
verifying "stack.cpp";

resource nodes<T>(p: Node<T>*) {
    field items: List<T>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns allocation(p, sizeof(Node<T>));
            owns *p;
            owns tail: nodes<T>(p->next);
            fact p != 0;
            fact aligned(p, 8);
            fact p->value == value;
            fact tail.items == rest;
        },
    }
}

function length<T>(xs: List<T>) -> Integer
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(value, rest) => length(rest) + 1,
    }
}

theorem length_nonnegative<T>(xs: List<T>) {
    ensures length(xs) >= 0 by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(length(List<T>::Nil));
                close();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<T>::Cons(value, rest)));
                close() using { length(rest) >= 0; };
            }
        }
    }
}

function first_or<T>(xs: List<T>, fallback: T) -> T {
    match xs {
        List::Nil => fallback,
        List::Cons(value, rest) => value,
    }
}

function is_cons<T>(xs: List<T>) -> Bool {
    match xs {
        List::Nil => false,
        List::Cons(value, rest) => true,
    }
}

function rest<T>(xs: List<T>) -> List<T> {
    match xs {
        List::Nil => List<T>::Nil,
        List::Cons(value, tail) => tail,
    }
}

template<class T> void Stack<T>::push(T value) {
    owns *this;
    consumes before: nodes<T>(this->head);
    produces after: nodes<T>(this->head);
    requires length(before.items) < 1000000;
    requires to_integer(this->count) == length(before.items);
    ensures after.items == List::Cons(value, old(before.items));
    ensures to_integer(this->count) == length(after.items);
} by {
    step_until(function.exit);
    let after = fold(nodes<T>(this->head), { items: List::Cons(value, old(before.items)), tail: before });
    unfold(length(List<T>::Cons(value, old(before.items))));
    have to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
    have to_integer(old(this->count) + 1u64) == length(List::Cons(value, old(before.items))) by close() using {
        to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
        to_integer(old(this->count)) == length(old(before.items));
        length(List::Cons(value, old(before.items))) == length(old(before.items)) + 1;
    };
    close();
}

template<class T> bool Stack<T>::pop(T& out) {
    owns *this;
    owns out;
    consumes before: nodes<T>(this->head);
    produces after: nodes<T>(this->head);
    requires to_integer(this->count) == length(before.items);
    ensures result == true;
    ensures out == first_or(old(before.items), old(out));
    ensures after.items == rest(old(before.items));
    ensures to_integer(this->count) == length(after.items);
} by {
    match before.items {
        List::Nil => {
            unfold(before);
            step_until(function.exit);
            let after = fold(nodes<T>(this->head), { items: List<T>::Nil });
            unfold(length(List<T>::Nil));
            unfold(is_cons(List<T>::Nil));
            unfold(first_or(List<T>::Nil, old(out)));
            unfold(rest(List<T>::Nil));
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
                    let after = fold(nodes<T>(this->head), { items: List<T>::Nil });
                    unfold(length(List<T>::Nil));
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
                    let after = fold(nodes<T>(this->head), { items: List::Cons(next_value, next_items), tail: next });
                    have to_integer(old(this->count)) == length(tail_items) + 1 by close() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                    };
                    have to_integer(1u64) <= to_integer(old(this->count)) by close() using {
                        to_integer(old(this->count)) == length(tail_items) + 1;
                        length(tail_items) >= 0;
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

template<class T> Stack<T>::~Stack() {
    owns *this;
    consumes list: nodes<T>(this->head);
} by {
    loop {
        owns *this;
        owns list: nodes<T>(this->head);
        decreases length(list.items);

        initialize by close();
        maintain by {
            match list.items {
                List::Nil => { contradiction(list.items == List<T>::Nil); },
                List::Cons(value, rest) => {
                    let { tail: tail } = unfold(list);
                    unfold(length(List::Cons(value, rest)));
                    apply(length_nonnegative(rest));
                    have 0 <= length(tail.items) by close();
                    have length(tail.items) < length(List::Cons(value, rest)) by close() using {
                        length(List::Cons(value, rest)) == length(rest) + 1;
                        tail.items == rest;
                    };
                    step();
                    step();
                    step();
                },
            }
        }
    }
    unfold(list);
    close();
}

template<class T> unsigned long Stack<T>::size() const {
    views *this;
    ensures result == this->count;
}

int round_trip(int x) {
    ensures result == x;
} by {
    step_until(region(2).entry);
    let empty = fold(nodes<int>(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by close() using { length(List<int32>::Nil) == 0; };
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    unfold(first_or(List<int32>::Cons(x, List<int32>::Nil), 0));
    close();
}

unsigned long pushed_size(int x) {
    ensures to_integer(result) == 2;
} by {
    step_until(region(2).entry);
    let empty = fold(nodes<int>(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by close() using { length(List<int32>::Nil) == 0; };
    step_until(region(3).entry);
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    have length(List<int32>::Cons(x, List<int32>::Nil)) < 1000000 by close() using {
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))));
    have length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == 2 by close() using {
        length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == length(List<int32>::Cons(x, List<int32>::Nil)) + 1;
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    close();
}
```

```expect
fail: `ensures result == true` failed for `Stack<T>::pop.ensures_0`
```
