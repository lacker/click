# execute certificate for a break in a nested loop branch

The `execute()` tactic must emit a certificate that the checker accepts when a
`break` occurs inside an `if` nested in a `while`.

```c filename=execute_nested_while_break_certificate.c
int32 stop_at_three() {
    int32 i = 0;
    while (i < 4) {
        if (i == 2) {
            break;
        }
        i++;
    }
    return i;
}
```

```click
verifying "execute_nested_while_break_certificate.c";

int32 stop_at_three() {
    ensures result == 2 by {
        execute();
        simp();
    }
}
```

```expect
pass
```
