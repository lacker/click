# Abstract callback contracts retain const through refinement and ordinary calls

The callback explicitly returns a resource that promises a typed readable
place for its result. Address equality remains a separate value claim;
refinement and ordinary calls preserve the result's const qualification.

```c filename=main.c
int read_view(const int *(*f)(const int *), const int *p) { return f(p)[0]; }
```

```click
resource readable(p: const int*) {
    views p[0..1];
}
contract const int *Exact(const int *p) {
    views p[0..1];
    produces readable(result);
    ensures result == p;
}
contract const int *Readable(const int *p) {
    views p[0..1];
    produces readable(result);
    ensures result == p;
}
theorem lift(callback: const int* (*)(const int*)) executes callback(const int* p) {
    requires Exact(callback);
    ensures Readable(callback) by { step(Exact); simp(); }
}
verifying "main.c";
int read_view(const int *(*f)(const int *), const int *p) {
    requires Exact(f);
    views p[0..1];
    ensures result == p[0];
} by { let returned = step(f(p), {}); unfold(readable(returned)); execute(); simp(); }
```

```expect
pass
```
