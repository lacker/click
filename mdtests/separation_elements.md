# Unequal array indices separate complete elements

```c filename=keep.c
void keep(unsigned char *bytes, unsigned long i, unsigned long k) { bytes[i] = 0; }
```

```click
import click::separation;
verifying "keep.c";
void keep(uint8* bytes, uint64 i, uint64 k) {
    owns bytes[0..4];
    requires 0 <= k and k < i and i < 4;
} by {
    have separate(memory(*(bytes + i)), memory(*(bytes + k))) by {
        have i != k by { close() using { k < i; }; }
        apply(separation::separate_elements(bytes, i, k));
        close();
    }
    mark before;
    step();
    have separate(statement(0).footprint, memory(*(bytes + k))) by {
        close() using { separate(memory(*(bytes + i)), memory(*(bytes + k))); };
    }
    have bytes[k] == at(before, bytes[k]) by {
        preserve(memory(*(bytes + k)), statement(0));
    }
    step_until(function.exit);
    close();
    close(); close(); close();
}
```

```expect
pass
```
