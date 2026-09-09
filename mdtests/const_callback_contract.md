# Abstract callback contracts retain const through refinement and ordinary calls

```c filename=main.c
int read_view(const int *(*f)(const int *), const int *p) { return f(p)[0]; }
```

```click
contract const int *Exact(const int *p) {
    views p[0..1];
    ensures result == p;
}
contract const int *Readable(const int *p) {
    views p[0..1];
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
} by { apply(lift(f)); step(Readable); execute(); simp(); }
```

```expect
pass
```
