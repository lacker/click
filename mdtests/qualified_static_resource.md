# A resource can own private storage in multiple files

```c filename=left.c
static unsigned long count = 7;
void clear(void) { count = 0; }
```

```c filename=right.c
static unsigned long count = 19;
unsigned long read_right(void) { return count; }
```

```c filename=main.c
void clear(void);
unsigned long read_right(void);
int main(void) { clear(); return read_right() == 19; }
```

```click
verifying "left.c" as left;
verifying "right.c" as right;
verifying "main.c";

resource both() {
    owns &left::count[0..1];
    owns &right::count[0..1];
    fact right::count == 19u64;
}

void clear() {
    owns both();
    ensures left::count == 0u64;
    ensures right::count == old(right::count);
} by { unfold(both()); execute(); fold(both()); simp(); }

unsigned long read_right() {
    owns both();
    ensures result == old(right::count);
    ensures result == 19u64;
} by { unfold(both()); execute(); fold(both()); simp(); }

int main() {
    ensures result == 1;
} by { fold(both()); execute(); simp(); }
```

```expect
pass
```
