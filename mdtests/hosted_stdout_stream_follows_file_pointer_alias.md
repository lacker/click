# Hosted stdout supplies one stream for ordinary FILE pointer aliases

```c filename=stream.c
#include <stdio.h>

static int initialized;

FILE *keep_stream(FILE *file)
{
    return file;
}

int main(void)
{
    FILE *file = stdout;
    initialized = 1;
    if (initialized != 1) {
        return 0;
    }
    return keep_stream(file) == stdout;
}
```

```click
verifying "stream.c";
import click::c::stdio::{stream};

FILE* keep_stream(FILE* file) {
    owns out: stream(file);
    ensures result == file;
    ensures out.write_history == old(out.write_history);
}

int32 main() {
    owns out: stream(stdout);
    ensures result == 1;
    ensures out.write_history == List::Nil;
}
```

```expect
pass
```
