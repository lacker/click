# Header-inline const returns retain qualification under internal names

```c filename=view.h
static inline const int *view(int *p) { return p; }
```

```c filename=caller.c
#include "view.h"
const int *caller(int *p) { return view(p); }
```

```click
verifying "caller.c";
const int *caller(int *p) { ensures result == p; } by { execute(); simp(); }
```

```expect
pass
```
