# A step can bind a call result using ordinary resource selection

The caller holds one instance for the callee's named resource. The step binds
the returned value while using the same default resource selection as bare
`step()`.

```c filename=step_default_resource.c
int32 read_status(int32* p) { return 7; }
int32 run(int32* p) {
    int32 x;
    x = read_status(p);
    x = 0;
    return x;
}
```

```click
verifying "step_default_resource.c";

resource cell(p: int32*) { field tag: int32; owns p[0..1]; }

int32 read_status(int32* p) {
    owns input: cell(p);
    ensures result == 7;
}

int32 run(int32* p) {
    owns c: cell(p);
    ensures result == 0;
} by {
    step();
    let { result: saved } = step();
    step_until(function.exit);
    have saved == 7 by { close(); }
    close();
}
```

```expect
pass
```
