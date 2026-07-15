# read resources

This checks the first viewed permission slice. A view permits
external loads and makes the covered memory loadable, but it does not grant write
permission.

```c filename=read_first.c
int32 read_first(int32 p[]) {
    return p[0];
}
```

```click
verifying "read_first.c";

int32 read_first(int32 p[]) {
    views p[0..1];

}
```

```expect
pass
```
