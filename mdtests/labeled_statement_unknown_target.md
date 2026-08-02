# unknown statement label diagnostic

```c filename=labeled_statement_unknown_target.c
int32 labeled_statement_unknown_target(int32 x) {
    return x;
}
```

```click
verifying "labeled_statement_unknown_target.c";

int32 labeled_statement_unknown_target(int32 x) {
    ensures result == x by {
        execute_until(missing);
        execute();
        simp();
    }
}
```

```expect
fail: unknown code region label `missing`
```
