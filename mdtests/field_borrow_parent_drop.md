# Updated fields are observed by the parent cleanup

This isolates the shared memory checker used by Rust field borrows. Updating a guard's
saved field to 42 must be observed by its cleanup through the stored pointer.
This pins the alias/state part of the checker gap; call-havoc cache
invalidation has a separate kernel regression. The ordinary nested Rust Guard
source remains covered by the Rust import integration regression.

```cpp filename=field_drop.cpp function=cleanup profile=scalar_int32
struct Guard {
    int* slot;
    int saved;
    explicit Guard(int& value) noexcept : slot(&value), saved(1) {}
    ~Guard() noexcept { *slot = saved; }
};
int cleanup(int& value) {
    {
        Guard parent(value);
        parent.saved = 42;
    }
    return value;
}
```

```click
verifying "field_drop.cpp";
Guard::Guard(int32& value) {
    owns this->slot;
    owns this->saved;
    ensures this->slot == &value;
    ensures this->saved == 1;
}
Guard::~Guard() {
    owns this->slot;
    owns this->saved;
    owns this->slot[0..1];
    ensures this->slot == old(this->slot);
    ensures this->saved == old(this->saved);
    ensures this->slot[0] == old(this->saved);
}
int32 cleanup(int32& value) {
    owns value;
    ensures value == 42;
}
```

```expect
pass
```
