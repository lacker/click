# Closing a viewed scope does not establish a false return postcondition

```c filename=completed_scope.c
void repair(void) { }
void finish(int32* p) { repair(); }
```

```click
verifying "completed_scope.c";
resource viewed(p: int32*) { views p[0..1]; }
resource marker() { field value: int32; }
void repair() {
    produces tag: marker();
    ensures tag.value == 1;
} by {
    step_until(function.exit);
    let tag = fold(marker(), { value: 1 });
    close();
}
void finish(int32* p) {
    views viewed(p);
    produces tag: marker();
    ensures tag.value == 2;
} by {
    with(viewed(p)) {
        let { tag: tag } = step(repair);
    }
}
```

```expect
fail: tag.value == 2
```
