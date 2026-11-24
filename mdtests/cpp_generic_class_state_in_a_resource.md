# A C++ class template's object state may live in a resource it holds

`Container<T>` declares its object's state, its `items`, a `List<T>`.
`Stack<T>` keeps its items in nodes on the heap, which no field of the
stack holds: its `class` block names the resource that holds them beside its
own memory, `resource state: nodes<T>(this->head);`, and defines `items`
from it. `Stack<T>`'s overrides are verified once with `T` abstract, each
holding `*this` and `state`. A caller passing a `Stack<int>` as a
`Container<int>&` lends its memory and its nodes, packed into the object,
and gets back a `nodes<int>` instance holding the object's new items, which
its own `state` takes.

`Container<T>` also declares `size`, which `Stack<T>` defines as its `count`
field, and its interface keeps `to_integer(size(this)) ==
length(items(this))`: each override restores it, `push` incrementing the
count as it conses and `pop` decrementing it as it takes the tail.
`pushed_size` reads the new size through a `Container<int>&`.

`Stack<T>`'s destructor deletes the remaining nodes and is verified once,
consuming them. `local_round_trip` builds a `Stack<int>` from its default
member initializers, folds its empty nodes as `state` before passing it as a
`Container<int>&`, and the destructor consumes the nodes the unpack gave
back at its return.

```cpp filename=containers.cpp function=caller;local_round_trip;pushed_size profile=normal_only templates=Container<T>;Stack<T>
template<class T> struct Node {
    T value;
    Node* next;
};
template<class T> struct Container {
    virtual void push(T value) noexcept = 0;
    virtual bool pop(T& out) noexcept = 0;
    virtual unsigned long size() const noexcept = 0;
};
template<class T> class Stack : public Container<T> {
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
    void push(T value) noexcept override {
        head = new Node<T>{value, head};
        count = count + 1;
    }
    bool pop(T& out) noexcept override {
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
    unsigned long size() const noexcept override { return count; }
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
int local_round_trip(int x) noexcept {
    Stack<int> stack;
    return round_trip(stack, x);
}
unsigned long pushed_size(Container<int>& container, int x) noexcept {
    container.push(x);
    return container.size();
}
```

```click
verifying "containers.cpp";
import click::integer;
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
template<class T> class Container<T> {
    function items(this) -> List<T>;
    function size(this) -> uint64;
}
template<class T> extern void Container<T>::push(T value) {
    requires to_integer(size(this)) == length(items(this));
    requires size(this) < 18446744073709551615u64;
    ensures to_integer(size(this)) == length(items(this));
    ensures items(this) == List::Cons(value, old(items(this)));
}
template<class T> extern bool Container<T>::pop(T& out) {
    owns out;
    requires to_integer(size(this)) == length(items(this));
    ensures to_integer(size(this)) == length(items(this));
    ensures result == is_cons(old(items(this)));
    ensures out == first_or(old(items(this)), old(out));
    ensures items(this) == rest(old(items(this)));
}
template<class T> extern unsigned long Container<T>::size() const {
    requires to_integer(size(this)) == length(items(this));
    ensures result == size(this);
}
template<class T> class Stack<T> : Container<T> {
    resource state: nodes<T>(this->head);
    function items(this) -> List<T> { state.items }
    function size(this) -> uint64 { this->count }
}
template<class T> void Stack<T>::push(T value) {
} by {
    match state.items {
        List::Nil => {
            unfold(state);
            step_until(function.exit);
            let tail = fold(nodes<T>(this->head->next), { items: List<T>::Nil });
            let state = fold(nodes<T>(this->head), { items: List::Cons(value, List<T>::Nil), tail: tail });
            unfold(length(List::Cons(value, List<T>::Nil)));
            have to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
            close();
        },
        List::Cons(top, below) => {
            // Keep the old list packaged while constructing its new head.
            let { tail: rest } = unfold(state);
            let prior = fold(nodes<T>(this->head), { items: List::Cons(top, below), tail: rest });
            step_until(function.exit);
            have this->head->next == old(this->head);
            let state = fold(nodes<T>(this->head), { items: List::Cons(value, List::Cons(top, below)), tail: prior });
            unfold(length(List::Cons(value, List::Cons(top, below))));
            have to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
            close();
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
            unfold(length(List::Cons(value, tail_items)));
            apply(length_nonnegative(tail_items));
            have to_integer(this->count) >= 1 by close() using {
                to_integer(this->count) == length(List::Cons(value, tail_items));
                length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                length(tail_items) >= 0;
            };
            let { tail: tail } = unfold(state);
            step_until(function.exit);
            unfold(is_cons(List::Cons(value, tail_items)));
            unfold(first_or(List::Cons(value, tail_items), old(out)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let state = fold(nodes<T>(this->head), { items: List<T>::Nil });
                    have to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                    unfold(length(List<T>::Nil));
                    have to_integer(old(this->count) - 1u64) == 0 by close() using {
                        to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - 1;
                        to_integer(old(this->count)) == length(List::Cons(value, List<T>::Nil));
                        length(List::Cons(value, List<T>::Nil)) == length(List<T>::Nil) + 1;
                        length(List<T>::Nil) == 0;
                    };
                    close();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let state = fold(nodes<T>(this->head), { items: List::Cons(next_value, next_items), tail: next });
                    have to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                    have to_integer(old(this->count) - 1u64) == length(List::Cons(next_value, next_items)) by close() using {
                        to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - 1;
                        to_integer(old(this->count)) == length(List::Cons(value, List::Cons(next_value, next_items)));
                        length(List::Cons(value, List::Cons(next_value, next_items))) == length(List::Cons(next_value, next_items)) + 1;
                    };
                    close();
                },
            }
        },
    }
}
template<class T> unsigned long Stack<T>::size() const {
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
                    mark before_node;
                    step();
                    have separate(region(1).footprint, memory(this->head)) by { close() using {}; }
                    have this->head == at(before_node, this->head) by {
                        preserve(memory(this->head), region(1));
                    }
                    have separate(region(1).footprint, memory(this->head->next)) by { close() using {}; }
                    have this->head->next == at(before_node, this->head->next) by {
                        preserve(memory(this->head->next), region(1));
                    }
                    have node == this->head by { close(); }
                    step();
                    have this->head == at(before_node, this->head->next) by { close(); }
                    // Delete affects the whole typed node, not just its first scalar cell.
                    have at(region(1).exit, separate(memory(*this->head), memory(this->head))) by { close(); }
                    mark before_delete;
                    step();
                    have separate(region(3).footprint, memory(this->head)) by {
                        close() using { at(region(1).exit, separate(memory(*this->head), memory(this->head))); };
                    }
                    have this->head == at(before_delete, this->head) by {
                        preserve(memory(this->head), region(3));
                    }
                    have this->head == at(before_node, this->head->next) by { close(); }
                },
            }
        }
    }
    unfold(list);
    step();
    close();
}
int round_trip(Container<int>& container, int x) {
    requires to_integer(size(container)) == length(items(container));
    requires size(container) < 18446744073709551615u64;
    ensures result == first_or(List::Cons(x, old(items(container))), 0);
}
int caller(Stack<int>& stack, int x) {
    owns stack;
    owns state: nodes<int>(stack.head);
    requires to_integer(stack.count) == length(state.items);
    requires stack.count < 18446744073709551615u64;
    ensures result == x;
} by {
    step_until(call(Stack__int__click_pack__Container__int, 0).entry);
    let { object_resource(): packed } = step(Stack__int__click_pack__Container__int, { state: state });
    step_until(function.exit);
    unfold(first_or(List<int>::Cons(x, old(state.items)), 0));
    close();
}
int local_round_trip(int x) {
    ensures result == x;
} by {
    step_until(region(2).entry);
    let state = fold(nodes<int>(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    step_until(call(Stack__int__click_pack__Container__int, 0).entry);
    let { object_resource(): packed } = step(Stack__int__click_pack__Container__int, { state: state });
    step_until(function.exit);
    unfold(first_or(List<int32>::Cons(x, List<int32>::Nil), 0));
    close();
}
unsigned long pushed_size(Container<int>& container, int x) {
    requires to_integer(size(container)) == length(items(container));
    requires size(container) < 18446744073709551615u64;
    ensures to_integer(result) == length(old(items(container))) + 1;
} by {
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, old(items(container)))));
    close();
}
```

```expect
pass
```
