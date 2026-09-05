# File-scope struct pointers retain identity through returns

```c filename=global_struct_pointer_return.c
struct node {
    int32 key;
};

struct node* current = 0;

struct node* get_current() {
    return current;
}

struct node* relay_current() {
    return get_current();
}
```

```click
verifying "global_struct_pointer_return.c";

struct node* get_current() {
    ensures result == current;
} by auto;

struct node* relay_current() {
    ensures result == current;
} by auto;
```

```expect
pass
```
