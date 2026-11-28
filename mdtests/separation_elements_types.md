# Element separation retains the instantiated storage width

```c filename=elements.c
struct item { unsigned char tag; long value; };
void inspect(struct item *p, unsigned long i, unsigned long j) {}
```

```click
import click::separation;
verifying "elements.c";

theorem words(p: int64*, i: uint64, j: uint64) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j])) by {
        apply(separation::separate_elements(p, i, j));
        close();
    }
}
theorem pointers(p: int32**, i: uint64, j: uint64) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j])) by {
        apply(separation::separate_elements(p, i, j));
        close();
    }
}
void inspect(struct item* p, uint64 i, uint64 j) {
    requires i != j;
    ensures true;
} by {
    have separate(memory(p[i]), memory(p[j])) by {
        apply(separation::separate_elements(p, i, j));
        close();
    }
    step_until(function.exit);
    close();
    close(); close(); close();
}
```

```expect
pass
```
