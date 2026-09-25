# A value equality grants no permission to read it in C

The precondition constrains a logical value. It supplies neither a viewed
resource nor an initialized allocation for the program's actual load.

```c filename=logical_value_fact_does_not_authorize_c_read.c
int32 read_cell(int32 *p) {
    return p[0];
}
```

```click
verifying "logical_value_fact_does_not_authorize_c_read.c";
int32 read_cell(int32 *p) {
    requires p[0] == 7;
    ensures result == 7;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
