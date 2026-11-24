# Verified outputs retain the caller's frame

The returned pointer has no equality postcondition relating it to `p`.
The verified resource-transfer rule nevertheless returns its owned cell beside
the caller's retained `q` and local struct. The caller does not reconstruct
that relationship from pointer geometry.

```c filename=verified_output_frame.c
struct holder { int *p; };
struct holder wrap(int *p) {
    struct holder h;
    h.p = p;
    return h;
}
int caller(int *p, int *q) {
    struct holder h = wrap(p);
    return 0;
}
```

```click
resource cell(p: int32*) { owns *p; }
verifying "verified_output_frame.c";
struct holder wrap(int32* p) {
    consumes cell(p);
    produces cell(result.p);
}
int32 caller(int32* p, int32* q) {
    consumes cell(p);
    owns *q;
    ensures result == 0;
} by { step_until(function.exit); close(); }
```

```expect
pass
```
