# Const pointer returns retain their view through direct and nested calls

```c filename=view.h
const int *view(int *p);
```

```c filename=view.c
#include "view.h"
const int *view(int *p) { return p; }
```

```c filename=caller.c
#include "view.h"
const int *relay(int *p) { return view(p); }
const int *assigned(int *p) { const int *q = p; q = view(p); return q; }
int read_view(int *p) { return view(p)[0]; }
```

```click
verifying "view.c";
verifying "caller.c";

const int *view(int *p) {
    requires loadable(p[0..1]);
    ensures result == p;
    ensures loadable(result[0..1]);
} by { execute(); simp(); }

const int *relay(int *p) {
    requires loadable(p[0..1]);
    ensures result == p;
} by { execute(); simp(); }

const int *assigned(int *p) {
    requires loadable(p[0..1]);
    ensures result == p;
} by { execute(); simp(); }

int read_view(int *p) {
    views p[0..1];
    ensures result == p[0];
} by { execute(); simp(); }
```

```expect
pass
```
