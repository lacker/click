# A linked pointer initializer cannot name another file's private object

`exposed` is initialized in `data.c` with the address of `value`, which is
private to `other.c`. The initializer is resolved in `data.c`, where no
`value` is visible, so it is refused there; linking does not let it borrow
another file's private name.

```c filename=other.c
static int value = 11;
int read_value(void) { return value; }
```

```c filename=data.c
int *exposed = &value;
```

```c filename=main.c
extern int *exposed;
int main(void) { return 0; }
```

```click
verifying "other.c";
verifying "data.c";
verifying "main.c";
int main() { ensures result == 0; }
by { execute(); simp(); }
```

```expect
fail: failed to parse C source `data.c`
```
