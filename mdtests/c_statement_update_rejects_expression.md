# C update expressions are rejected

This documents the update-sugar boundary. C0 accepts `i++` and compound
assignment as standalone statements, but does not model full C expression
side effects such as using the old value of `i++` inside another assignment.

```c filename=statement_update_rejects_expression.c
int32 statement_update_rejects_expression() {
    int32 i;
    int32 j;
    i = 0;
    j = i++;
    return j;
}
```

```click
verifying "statement_update_rejects_expression.c";

int32 statement_update_rejects_expression() {
    ensures result == 0 by auto;
}
```

```expect
fail: expected Semicolon, got PlusPlus
```
