# A known const-returning address can be passed to an abstract callback caller

```c filename=main.c
const int *view(int *p) { return p; }
int use_view(const int *(*f)(int *), int *p) { return f(p)[0]; }
int caller(int *p) { return use_view(&view, p); }
```

```click
contract const int *View(int *p) { ensures result == p; }
verifying "main.c";
const int *view(int *p) { ensures result == p; } by { execute(); simp(); }
int use_view(const int *(*f)(int *), int *p) {
    requires View(f);
    views p[0..1];
    ensures result == p[0];
} by { execute(); simp(); }
int caller(int *p) { views p[0..1]; ensures result == p[0]; } by { execute(); simp(); }
```

```expect
pass
```
