# A literal printf requires ownership of the stream

```c filename=unowned.c
#include <stdio.h>

int main(void)
{
    printf("hello");
    return 0;
}
```

```click
verifying "unowned.c";

int32 main() {
    ensures result == 0;
}
```

```expect
fail: has an unbound instance binder `out`
```
