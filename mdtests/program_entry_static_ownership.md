# Program startup owns initialized static storage

```c filename=main.c
unsigned int counter = 7;
unsigned int bump(unsigned int *p) { *p += 1; return *p; }
int main(void) { bump(&counter); return bump(&counter); }
```

```click
verifying "main.c";
unsigned int bump(unsigned int *p) {
    requires loadable(p[0..1]);
    consumes p[0..1];
    produces p[0..1];
    ensures p[0] == old(p[0]) + 1u32;
    ensures result == p[0];
    ensures result == old(p[0]) + 1u32;
} by { execute(); simp(); }
int main() {
    ensures result == 9;
} by {
    step();
    mark first;
    have counter == 8u32 by simp;
    execute();
    have result == at(first, counter) + 1u32 by simp;
    rewrite(result == at(first, counter) + 1u32);
    rewrite(at(first, counter) == 8u32);
    simp();
}
```

```expect
pass
```
