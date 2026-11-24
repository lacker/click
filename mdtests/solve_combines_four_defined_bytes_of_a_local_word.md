# `solve` uses the four defined bytes of a local `uint32`

The helper’s contract certifies each byte separately. The caller can use all
four facts at the same point to read the declared word.

```c filename=defined_word.c
void write(unsigned char *p) {
    p[0] = 1;
    p[1] = 2;
    p[2] = 3;
    p[3] = 4;
}
void check(void) {
    unsigned int obj;
    write((unsigned char *)(void *)&obj);
}
```

```click quick-solve
verifying "defined_word.c";

void write(uint8* p) {
    owns uninitialized(p[0..4]);
    ensures defined(p[0]);
    ensures defined(p[1]);
    ensures defined(p[2]);
    ensures defined(p[3]);
}
void check() {
    ensures at(call(0).exit,
        defined(load<uint32>(("defined_word.c"::check.local(0).storage(implicit) as (uint32 *))))
    );
} by {
    step_until(call(0).entry);
    step();
    step_until(function.exit);
    close();
}
```

```expect
pass
```
