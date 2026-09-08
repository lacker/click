# Version header replacement macros

String and expression replacements compose with aliases and continued lines.
This synthetic regression uses the modeled unsigned-byte return type. Plain
char and const-qualified returns remain unsupported; the unchanged json-c
example separately records those boundaries. It is not a translated json-c API.

```c filename=version.h
#ifndef VERSION_H
#define VERSION_H
#define MINOR 17
#define NUMBER \
    ((0 << 16) | (MINOR << 8) | 0)
#define TEXT "0.17"
#define EXPORT extern
EXPORT int version_num(void);
EXPORT unsigned char *version_text(void);
#endif
```

```c filename=version.c
#include "version.h"
int version_num(void) { return NUMBER; }
unsigned char *version_text(void) { return TEXT; }
```

```click
verifying "version.c";

int version_num() {
    ensures result == 4352;
} by { execute(); simp(); }

unsigned char *version_text() {
    ensures readable: loadable(result[0..5]);
    ensures result[0] == '0';
    ensures result[1] == '.';
    ensures result[2] == '1';
    ensures result[3] == '7';
    ensures result[4] == '\0';
} by { execute(); simp(); }
```

```expect
pass
```
