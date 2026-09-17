# Calls through fields retain const-return and const-parameter types

```c filename=main.c
struct reader { const int *(*view)(const int *); };
const int *view(const int *p) { return p; }
int read_view(struct reader *r, const int *p) {
    r->view = &view;
    const int *q = r->view(p);
    return q[0];
}
```

```click
verifying "main.c";
const int *view(const int *p) { ensures result == p; } by { execute(); simp(); }
int read_view(struct reader *r, const int *p) { owns object(r); views p[0..1]; ensures result == old(p[0]); } by { execute(); simp(); }
```

```expect
pass
```
