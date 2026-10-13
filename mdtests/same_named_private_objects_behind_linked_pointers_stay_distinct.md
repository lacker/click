# Same-named private objects behind linked pointers stay distinct

Two files each define a private `value` and export its address. Each
initializer is resolved in its own file, so the two pointers name two
objects, and `main` reads 3 through one and 4 through the other.

```c filename=first.c
static int value = 3;
int *first = &value;
```

```c filename=second.c
static int value = 4;
int *second = &value;
```

```c filename=main.c
extern int *first;
extern int *second;
int read_cell(int *p) { return *p; }
int main(void) {
    int a = read_cell(first);
    int b = read_cell(second);
    return a * 10 + b;
}
```

```click
verifying "first.c";
verifying "second.c";
verifying "main.c";
int read_cell(int *p) {
    requires viewable(p[0..1]);
    consumes p[0..1];
    produces p[0..1];
    ensures result == old(p[0]);
} by { execute(); simp(); }
int main() { ensures result == 34; }
by { execute(); simp(); }
```

```expect
pass
```
