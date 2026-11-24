# A statement region of a missing statement is refused

```c filename=statement_path_missing.c
int32 probe(int32 x) {
    return x;
}
```

```click
verifying "statement_path_missing.c";

int32 probe(int32 x) {
    ensures result == x;
} by {
    step();
    have at(statement(3).exit, x) == x by close();
    close();
}
```

```expect
fail: this function has no `statement(3)`
```
