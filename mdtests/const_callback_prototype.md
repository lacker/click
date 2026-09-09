# Cross-file prototypes cannot change a callback return qualifier

```c filename=api.h
int ignore(const int *(*f)(int *));
```

```c filename=main.c
#include "api.h"
int ignore(int *(*f)(int *)) { return 0; }
```

```click
verifying "main.c";
int ignore(int *(*f)(int *)) { ensures result == 0; }
```

```expect
fail: conflicting declarations
```
