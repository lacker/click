# a refused C statement is named where it was written

A refused step used to print only the C operation as Click checked it, so a
store to a field of a struct-array element read as a byte-offset store and
named no line. The refusal now also names the file, line, and column of the
statement it checked and quotes the statement as written, without its
comment. Positions are diagnostics only: moving the statement changes this
line and nothing else.

Here the overflowing addition is on line 3 of the C block. `click verify` on
this file names the line of the markdown file instead.

```c filename=a_refused_c_statement_is_named_where_it_was_written.c
int32 add(int32 a, int32 b) {
    int32 total;
    total = a + b; // may overflow
    return total;
}
```

```click
verifying "a_refused_c_statement_is_named_where_it_was_written.c";

int32 add(int32 a, int32 b) {
    ensures result == a + b;
} by {
    step(); step(); step(); simp();
}
```

```expect
fail: `step()` produced undefined behavior: signed overflow
  operation: `a + b`
  C statement at a_refused_c_statement_is_named_where_it_was_written.c:3:5: `total = a + b;`
```
