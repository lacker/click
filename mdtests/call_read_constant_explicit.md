# Explicit constant read across a modular call

```c filename=read.c
int32 read(int32 *p) { return *p; }
int32 caller(int32 *p) { *p = 7; int32 r = read(p); return r; }
```

```click
verifying "read.c";
int32 read(int32 *p) { views *p; ensures result == old(*p); }
int32 caller(int32 *p) { owns *p; ensures result == 7; } by {
    step();
    step();
    step();
    step();
    step();
    have result == 7 by {
        close();
    }
    close();
    close();
}
```

```expect
pass
```
