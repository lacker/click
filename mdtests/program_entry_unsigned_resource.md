# Startup resource regression

```c filename=main.c
unsigned int state[2] = {7, 9};
unsigned int read_pair(unsigned int *p) { return p[0] + p[1]; }
int main(void) { return read_pair(state); }
```

```click
resource pair(p: uint32*) { owns p[0..2]; }
verifying "main.c";
unsigned int read_pair(unsigned int *p) {
    requires loadable(p[0..2]);
    consumes pair(p);
    produces pair(p);
    ensures result == old(p[0]) + old(p[1]);
} by { unfold(pair(p)); execute(); fold(pair(p)); simp(); }
int main() {
    ensures result == 16;
} by { fold(pair(state)); execute(); simp(); }
```

```expect
pass
```

