# write resources split symbolic ranges

This checks that a caller can split out a symbolic one-cell subrange from a
larger write resource, pass it to a helper, and rejoin it after the helper
returns it.

```c filename=write_at.c
int32 write_at(int32 p[], int32 i) {
    p[i] = 1;
    return p[i];
}
```

```c filename=write_at_symbolic.c
int32 write_at_symbolic(int32 p[], int32 i, int32 n) {
    int32 value;
    value = write_at(p, i);
    return value;
}
```

```click
verifying "write_at.c";
verifying "write_at_symbolic.c";

int32 write_at(int32 p[], int32 i) {
    requires i >= 0;
    requires i < 2147483647;
    requires loadable(p[i..i + 1]);
    consumes p[i..i + 1];

    produces p[i..i + 1] by auto;
}

int32 write_at_symbolic(int32 p[], int32 i, int32 n) {
    requires i >= 0;
    requires i < n;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];

    produces p[0..n] by auto;
}
```

```expect
pass
```
