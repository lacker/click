# A generic push cannot claim it keeps its list

`Stack<T>::push`, proved once for every type over the generic resource
`nodes<T>`, puts its value at the front of the list. A contract claiming the
list is unchanged is refused at the abstract type, before any instance takes
it (`cpp_generic_resource_checked_once.md` proves the true one).

```cpp filename=stack.cpp function=pushed_size profile=normal_only templates=Stack<T>
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

    unsigned long size() const noexcept { return count; }
};

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

template<class T> void Stack<T>::push(T value) {
    owns *this;
    consumes before: nodes<T>(this->head);
    produces after: nodes<T>(this->head);
    requires length(before.items) < 1000000;
    requires to_integer(this->count) == length(before.items);
    ensures after.items == old(before.items);
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

template<class T> unsigned long Stack<T>::size() const {
    views *this;
    ensures result == this->count;
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
fail: `ensures after.items == old(before.items)` failed for `Stack<T>::push.ensures_0`
```
