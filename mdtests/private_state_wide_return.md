# Private mutating wrappers retain distinct linked storage

```c filename=left.c
struct counter { unsigned long value; };
static struct counter state = {7};
unsigned long bump(struct counter *p) { p->value += 1; return p->value; }
unsigned long left(void) { return bump(&state); }
```

```c filename=right.c
struct counter { unsigned long value; };
unsigned long bump(struct counter *p);
static struct counter state = {40};
unsigned long right(void) { return bump(&state); }
```

```c filename=main.c
unsigned long left(void);
unsigned long right(void);
int main(void) { left(); return right(); }
```

```click
verifying "left.c" as left_file;
verifying "right.c" as right_file;
verifying "main.c";

unsigned long bump(struct counter *p) {
    requires loadable(p->value);
    owns p->value;
    ensures p->value == old(p->value) + 1u64;
    ensures result == p->value;
    ensures result == old(p->value) + 1u64;
} by { execute(); simp(); }

unsigned long left() {
    owns left_file::state.value;
    ensures left_file::state.value == old(left_file::state.value) + 1u64;
    ensures result == left_file::state.value;
    ensures result == old(left_file::state.value) + 1u64;
} by { execute(); simp(); }

unsigned long right() {
    owns right_file::state.value;
    ensures right_file::state.value == old(right_file::state.value) + 1u64;
    ensures result == right_file::state.value;
    ensures result == old(right_file::state.value) + 1u64;
} by { execute(); simp(); }

int main() { ensures result == 41; }
by {
    have right_file::state.value == 40u64 by simp;
    step();
    have right_file::state.value == 40u64 by simp;
    step();
    have right_file::state.value == 41u64 by simp;
    step();
    simp();
}
```

```expect
pass
```
