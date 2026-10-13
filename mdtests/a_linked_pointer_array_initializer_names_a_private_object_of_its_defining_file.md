# A linked pointer array initializer names a private object of its defining file

An externally linked array of pointers is initialized in `data.c` with the
address of that file's private `value`. Its elements are resolved in
`data.c`, so `main.c` reads the private object through `table[0]`.

```c filename=data.c
static int value = 11;
int *table[1] = {&value};
```

```c filename=main.c
extern int *table[1];
int read_cell(int *p) { return *p; }
int main(void) {
    int *p = table[0];
    int cell = read_cell(p);
    return cell;
}
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
