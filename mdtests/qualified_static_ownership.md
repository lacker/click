# File aliases name private static storage

```c filename=counter.c
static int count = 7;
void reset(void) { count = 0; }
```

```c filename=cache.c
static int count[2] = {11, 12};
int read_cache(void) { return count[1]; }
```

```c filename=main.c
void reset(void);
int read_cache(void);
int main(void) { reset(); return read_cache(); }
```

```click
verifying "counter.c" as counter;
verifying "cache.c" as cache;
verifying "main.c";

void reset() {
    owns &counter::count[0..1];
    ensures counter::count == 0;
} by { execute(); simp(); }

int read_cache() {
    owns cache::count[0..2];
    ensures result == old(cache::count[1]);
} by { execute(); simp(); }

int main() {
    ensures result == 12;
} by { execute(); simp(); }
```

```expect
pass
```
