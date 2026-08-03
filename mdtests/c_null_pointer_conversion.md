# C null pointer conversion

The C0 integer constant `0` converts to the canonical null pointer in pointer
returns, initialization, assignment, and call arguments. Returning an already
typed pointer follows the same independently certified path.

```c filename=return_pointer.c
int32* return_pointer(int32* p) {
    return p;
}
```

```c filename=return_null.c
int32* return_null() {
    return 0;
}
```

```c filename=initialize_null.c
int32* initialize_null() {
    int32* p = 0;
    return p;
}
```

```c filename=assign_null.c
int32* assign_null(int32* p) {
    p = 0;
    return p;
}
```

```c filename=return_byte_null.c
uint8* return_byte_null() {
    return 0;
}
```

```c filename=clear_pointer.c
struct holder {
    int32* data;
};

int32 clear_pointer(struct holder* owner) {
    owner->data = 0;
    return owner->data == 0;
}
```

```c filename=pointer_is_null.c
int32 pointer_is_null(int32* p) {
    return p == 0;
}
```

```c filename=call_with_null.c
int32 call_with_null() {
    int32 result;
    result = pointer_is_null(0);
    return result;
}
```

```click
verifying "return_pointer.c";
verifying "return_null.c";
verifying "initialize_null.c";
verifying "assign_null.c";
verifying "return_byte_null.c";
verifying "clear_pointer.c";
verifying "pointer_is_null.c";
verifying "call_with_null.c";

int32* return_pointer(int32* p) {
    ensures result == p by auto;
}

int32* return_null() {
    ensures result == 0 by auto;
}

int32* initialize_null() {
    ensures result == 0 by auto;
}

int32* assign_null(int32* p) {
    ensures result == 0 by auto;
}

uint8* return_byte_null() {
    ensures result == 0 by auto;
}

int32 clear_pointer(struct holder* owner) {
    owns owner->data;
    mutable owner->data;

    ensures result == 1;
    ensures owner->data == 0;
} by {
    execute();
    frame();
    simp();
}

int32 pointer_is_null(int32* p) {
    requires p == 0;
    ensures result == 1;
} by auto;

int32 call_with_null() {
    ensures result == 1 by auto;
}
```

```expect
pass
```
