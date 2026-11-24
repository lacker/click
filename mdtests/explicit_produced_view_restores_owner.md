# Releasing a view returns the caller's exclusive ownership

```c filename=first_owned.c
int *first(int *left, int *right) { return left; }

void update(int *a, int *b) {
    int *p = first(a, b);
    *b = 7;
    *a = 9;
}
```

```click
import click::separation;
verifying "first_owned.c";

int32* first(int32* left, int32* right) {
    views *left as left_input;
    views *right;
    produces view(*result) from left_input;
    ensures result == left;
}

void update(int32* a, int32* b) {
    requires separate(memory(*a), memory(*b));
    owns *a;
    owns *b;
    ensures *a == 9;
    ensures *b == 7;
} by {
    step();
    step();
    release_view(*a);
    step();
    step_until(function.exit);
    close();
}
```

```expect
pass
```
