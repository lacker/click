# A write supplies separation from both active views

The borrowed footprint is a resource descriptor; combining two views here
asserts no ownership of that descriptor and does not require the views to be
separate from each other.

```c filename=explicit_write_separation_from_two_views.c
void set(int *p, int *q, int *r) { *p = 1; }
```

```click
import click::separation;
verifying "explicit_write_separation_from_two_views.c";
void set(int32* p, int32* q, int32* r) {
    owns *p;
    views *q;
    views *r;
} by {
    have separate(memory(*q), memory(*p)) by { close(); }
    have separate(memory(*r), memory(*p)) by { close(); }
    have separate(memory(*q) * memory(*r), memory(*p)) by {
        apply(separation::separate_star(memory(*q), memory(*r), memory(*p)));
    }
    have separate(memory(*p), memory(*q) * memory(*r)) by {
        apply(separation::separate_symm(memory(*q) * memory(*r), memory(*p)));
    }
    step();
}
```

```expect
pass
```
