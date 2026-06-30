# free permission consumption removes access

This checks the first deallocation-authority behavior. Passing `free(...)` to a
helper consumes that free resource and removes overlapping read/write access
from the caller context, so the caller cannot write the freed range afterward.

```c filename=release_first.c
int32 release_first(int32 p[]) {
    return 0;
}
```

```c filename=write_after_release.c
int32 write_after_release(int32 p[]) {
    int32 value;
    value = release_first(p);
    p[0] = 1;
    return p[0];
}
```

```click
verifying "release_first.c";
verifying "write_after_release.c";

int32 release_first(int32 p[]) {
    requires free(p[0..1]);

    ensures returns_zero: result == 0 by auto;
}

int32 write_after_release(int32 p[]) {
    requires write(p[0..1]);
    requires free(p[0..1]);

    ensures returns_written: result == 1 by auto;
}
```

```expect
fail: MissingResource
```
