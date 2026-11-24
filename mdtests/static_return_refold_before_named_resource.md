# A static ordinary return refold is retained before a named resource exchange

```c filename=refold.c
void inspect(int32* p) { }
```

```click
verifying "refold.c";
resource cell(p: int32*) { owns p[0..1]; }
resource marker() { field value: int32; }
void inspect(int32* p) {
    owns cell(p);
    produces tag: marker();
    ensures tag.value == 1;
} by {
    unfold(cell(p)); step_until(function.exit); fold(cell(p));
    let tag = fold(marker(), { value: 1 });
    close();
}
```

```expect
pass
```
