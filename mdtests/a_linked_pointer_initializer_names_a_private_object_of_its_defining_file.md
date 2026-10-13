# A linked pointer initializer names a private object of its defining file

`exposed` is defined in the data-only file `data.c` as the address of that
file's private `value`. `main.c` can name `exposed` but not `value`, so the
initializer is resolved in `data.c`, and `main` reads the private object
through the linked pointer, with startup ownership of its pointee. The C is
the original program unchanged: the call and the read of `zero` share one
expression.

```c filename=data.c
static int value = 11;
int *exposed = &value;
int zero;
```

```c filename=main.c
extern int *exposed;
extern int zero;
int read_cell(int *p) { return *p; }
int main(void) { return read_cell(exposed) + zero; }
```

```click
verifying "data.c";
verifying "main.c";
int read_cell(int *p) {
    requires viewable(p[0..1]);
    consumes p[0..1];
    produces p[0..1];
    ensures result == old(p[0]);
} by { execute(); simp(); }
int main() { ensures result == 11; }
by { execute(); simp(); }
```

```expect
pass
```
