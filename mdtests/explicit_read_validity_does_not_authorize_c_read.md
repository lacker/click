# Explicit read validity grants no resource permission

A pure typed-validity precondition does not grant the access resource needed
by the C load.

```c filename=explicit_read_validity_does_not_authorize_c_read.c
int32 read_cell(int32 *p) {
    return p[0];
}
```

```click
verifying "explicit_read_validity_does_not_authorize_c_read.c";
int32 read_cell(int32 *p) {
    requires defined(p[0]);
    ensures result == p[0];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
