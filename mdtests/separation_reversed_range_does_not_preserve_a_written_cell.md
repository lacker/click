# A reversed logical range cannot frame a write to a real cell

The reversed range is separate from the written cell. Its modular byte count
is four, but that does not make it a four-byte observation. The refusal must
happen at `preserve`, after the two separation facts have been established.

```c filename=overwritten.c
void overwrite(int32 *p) { *p = 1; }
```

```click
verifying "overwritten.c";
void overwrite(int32 *p) {
    owns *p;
    requires *p == 0;
    ensures *p == 0;
} by {
    step();
    have separate(memory(*p), memory(p[0..-1073741823])) by { close(); }
    have separate(statement(0).footprint, memory(p[0..-1073741823])) by {
        close();
    }
    have *p == old(*p) by {
        preserve(memory(p[0..-1073741823]), statement(0));
    }
    step();
    rewrite(*p, old(*p));
    close();
}
```

```expect
fail: preserve requires a region footprint separated from the selected complete observation
```
