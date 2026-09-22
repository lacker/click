# A wide array slice does not authorize writing its neighbor

```c filename=wide.c
struct words { char tag; unsigned long data[3]; };
void write_neighbor(struct words *p) { p->data[2] = 4294967296UL; }
```

```click
verifying "wide.c";
void write_neighbor(struct words *p) {
    owns p->data[1..2];
    views p->data[2..3];
    ensures p->data[2] == 4294967296 by auto;
}
```

```expect
fail: missing resource fact
```
