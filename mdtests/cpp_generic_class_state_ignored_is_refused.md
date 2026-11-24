# A class template whose state ignores the resource it holds is refused once

`Stack<T>` holds its nodes in `state` but defines `items` as the empty list.
`Stack<T>::push` is verified once for every type against `Container<T>`'s
interface read through that definition, which says the pushed value is on
top, and is refused there.

```cpp filename=containers_refused.cpp function=caller profile=normal_only templates=Container<T>;Stack<T>
template<class T> struct Node {
    T value;
    Node* next;
};
template<class T> struct Container {
    virtual void push(T value) noexcept = 0;
    virtual bool pop(T& out) noexcept = 0;
};
template<class T> class Stack : public Container<T> {
    Node<T>* head = nullptr;
public:
    void push(T value) noexcept override {
        head = new Node<T>{value, head};
    }
    bool pop(T& out) noexcept override {
        if (head == nullptr) {
            return false;
        }
        Node<T>* node = head;
        out = node->value;
        head = node->next;
        delete node;
        return true;
    }
};
int round_trip(Container<int>& container, int x) noexcept {
    container.push(x);
    int out = 0;
    container.pop(out);
    return out;
}
int caller(Stack<int>& stack, int x) noexcept {
    return round_trip(stack, x);
}
```

```click
verifying "containers_refused.cpp";
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
template<class T> class Container<T> {
    function items(this) -> List<T>;
}
template<class T> extern void Container<T>::push(T value) {
    ensures items(this) == List::Cons(value, old(items(this)));
}
template<class T> extern bool Container<T>::pop(T& out) {
    owns out;
    ensures result == is_cons(old(items(this)));
    ensures out == first_or(old(items(this)), old(out));
    ensures items(this) == rest(old(items(this)));
}
template<class T> class Stack<T> : Container<T> {
    resource state: nodes<T>(this->head);
    function items(this) -> List<T> { List<T>::Nil }
}
template<class T> void Stack<T>::push(T value) {
} by {
    match state.items {
        List::Nil => {
            unfold(state);
            step_until(function.exit);
            let tail = fold(nodes<T>(this->head->next), { items: List<T>::Nil });
            let state = fold(nodes<T>(this->head), { items: List::Cons(value, List<T>::Nil), tail: tail });
        },
        List::Cons(top, below) => {
            let { tail: rest } = unfold(state);
            step_until(function.exit);
            let tail = fold(nodes<T>(this->head->next), { items: List::Cons(top, below), tail: rest });
            let state = fold(nodes<T>(this->head), { items: List::Cons(value, List::Cons(top, below)), tail: tail });
        },
    }
}
template<class T> bool Stack<T>::pop(T& out) {
} by {
    match state.items {
        List::Nil => {
            unfold(state);
            step_until(function.exit);
            let state = fold(nodes<T>(this->head), { items: List<T>::Nil });
            unfold(is_cons(List<T>::Nil));
            unfold(first_or(List<T>::Nil, old(out)));
            unfold(rest(List<T>::Nil));
        },
        List::Cons(value, tail_items) => {
            let { tail: tail } = unfold(state);
            step_until(function.exit);
            unfold(is_cons(List::Cons(value, tail_items)));
            unfold(first_or(List::Cons(value, tail_items), old(out)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let state = fold(nodes<T>(this->head), { items: List<T>::Nil });
                    close();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let state = fold(nodes<T>(this->head), { items: List::Cons(next_value, next_items), tail: next });
                    close();
                },
            }
        },
    }
}
int round_trip(Container<int>& container, int x) {
    ensures result == first_or(List::Cons(x, old(items(container))), 0);
}
int caller(Stack<int>& stack, int x) {
    owns stack;
    owns state: nodes<int>(stack.head);
    ensures result == x;
} by {
    step_until(function.exit);
    unfold(first_or(List<int>::Cons(x, old(state.items)), 0));
    close();
}
```

```expect
fail: `Stack<T>::push.interface_ensures_0`
```
