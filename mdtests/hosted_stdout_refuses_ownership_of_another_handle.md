# Startup can only supply ownership of the modeled hosted stream

```c filename=other.c
#include <stdio.h>

FILE *other = 0;

int main(void)
{
    return 0;
}
```

```click
verifying "other.c";
import click::c::stdio::{stream};

int32 main() {
    owns out: stream(other);
    ensures result == 0;
}
```

```expect
fail: program-entry stream ownership requires the hosted stdout handle
```
