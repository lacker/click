```c filename=retry.c
struct box { int *child; };
void inspect(struct box *p) {}
```
```click
verifying "retry.c";
resource marker(p: int32*) {}
void inspect(struct box* p) {
    owns marker(p->child);
    owns p->child;
} by { execute(); simp(); }
```
```expect
pass
```
