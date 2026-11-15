# Saved memory bases keep current indices

The pointer is captured at entry or at a mark; the bounds belong to the state
where the descriptor is written. Reassigning the pointer and advancing the index
must not move either state's base or freeze the index at zero.

```c filename=saved_memory.c
void advance(int *p, int *q, int i) {
    p = q;
    i++;
}
```

```click
import click::separation;
verifying "saved_memory.c";
void advance(int32 *p, int32 *q, int32 i) {
    ensures true;
    requires i == 0;
    requires separate(memory(p[0..2]), memory(q[0..2]));
} by {
    mark before;
    step();
    step();
    have separate(memory(old(p)[0..2]), memory(q[0..2])) by { known(); }
    have separate(memory(at(before, p)[0..2]), memory(q[0..2])) by { known(); }
    have i == 1;
    have i != 0;
    have separate(memory(old(p)[i]), memory(old(p)[0])) by {
        apply(separation::separate_elements(old(p), i, 0)) using { i != 0; };
    }
    have separate(memory(at(before, p)[i]), memory(at(before, p)[0])) by {
        apply(separation::separate_elements(at(before, p), i, 0)) using { i != 0; };
    }
    have 0 <= i;
    have i <= 2;
    have contains(memory(old(p)[0..2]), memory(old(p)[i..2])) by {
        apply(separation::contains_subrange(old(p), 0, 2, i, 2)) using { 0 <= i; i <= 2; 2 <= 2; };
    }
    step();
}
```

```expect
pass
```
