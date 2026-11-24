# Established named contracts retain the caller's frame

`Transfer` returns an owned cell at an opaque pointer with no equality
postcondition. Its established contract fact supplies the joint frame rule
for both a selected direct call and an abstract callback call. The nominal
declaration and its discarded template body supply no proof themselves.

```c filename=named_output_frame.c
int *identity(int *p) { return p; }
int direct(int *p, int *q) {
    int *h = identity(p);
    return 0;
}
int refined(int *(*callback)(int *), int *p, int *q) {
    int *h = callback(p);
    return 0;
}
int indirect(int *(*callback)(int *), int *p, int *q) {
    int *h = callback(p);
    return 0;
}
```

```click
resource cell(p: int32*) { owns *p; }
verifying "named_output_frame.c";
contract int32* Transfer(int32* p) {
    consumes cell(p);
    produces cell(result);
}
contract int32* Forward(int32* p) {
    consumes cell(p);
    produces cell(result);
}
theorem transfer_is_forward(callback: int32* (*)(int32*)) {
    requires Transfer(callback);
    ensures Forward(callback) by {
        unfold(Transfer(callback));
        unfold(Forward(callback));
        close();
    }
}
int32* identity(int32* p) {
    consumes cell(p);
    produces cell(result);
}
theorem identity_has_transfer() executes identity(int32* p) {
    ensures Transfer(&identity) by { step_until(function.exit); close(); }
}
int32 direct(int32* p, int32* q) {
    consumes cell(p);
    owns *q;
    ensures result == 0;
} by {
    apply(identity_has_transfer());
    step();
    step(Transfer);
    step_until(function.exit); close();
}
int32 refined(int32* (*callback)(int32*), int32* p, int32* q) {
    requires Transfer(callback);
    consumes cell(p);
    owns *q;
    ensures result == 0;
} by {
    apply(transfer_is_forward(callback));
    step();
    step(Forward);
    step_until(function.exit); close();
}
int32 indirect(int32* (*callback)(int32*), int32* p, int32* q) {
    requires Transfer(callback);
    consumes cell(p);
    owns *q;
    ensures result == 0;
} by { step_until(function.exit); close(); }
```

```expect
pass
```
