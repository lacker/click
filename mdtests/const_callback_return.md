# Const-returning callbacks preserve identity and permit reads across prototypes

```c filename=view.h
const int *view(int *p);
```

```c filename=view.c
#include "view.h"
const int *view(int *p) { return p; }
```

```c filename=caller.c
#include "view.h"
const int *relay(int *p) {
    const int *(*f)(int *) = &view;
    return f(p);
}
int read_view(int *p) {
    const int *(*f)(int *) = &view;
    const int *q = f(p);
    q = f(p);
    return q[0];
}
int nested(int *p) {
    const int *(*f)(int *) = &view;
    return f(p)[0];
}
```

```click
verifying "view.c";
verifying "caller.c";
const int *view(int *p) { ensures result == p; } by { execute(); simp(); }
const int *relay(int *p) { ensures result == p; } by { execute(); simp(); }
int read_view(int *p) { views p[0..1]; ensures result == p[0]; } by { execute(); simp(); }
int nested(int *p) { views p[0..1]; ensures result == p[0]; } by { execute(); simp(); }
```

```expect
pass
```
