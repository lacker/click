# C statement update sugar

This checks the narrow C0 update-sugar slice. These forms are accepted only as
statements and lower to ordinary assignments:

- `i++;`
- `i--;`
- `i += expr;`
- `i -= expr;`
- `i *= expr;`

They do not introduce C expression side effects.

```c filename=statement_updates.c
int32 statement_updates() {
    int32 x;
    x = 1;
    x++;
    x += 4;
    x *= 3;
    x--;
    x -= 2;
    return x;
}
```

```c filename=for_increment_step.c
int32 for_increment_step() {
    int32 i;
    int32 total;
    total = 0;
    for (i = 0; i < 3; i++) {
        total += i;
    }
    return total;
}
```

```c filename=symbolic_statement_update.c
int32 symbolic_statement_update(int32 x) {
    x += 1;
    return x;
}
```

```click
verifying "statement_updates.c";
verifying "for_increment_step.c";
verifying "symbolic_statement_update.c";

int32 statement_updates() {
    ensures result == 15 by auto;
}

int32 for_increment_step() {
    ensures result == 3 by auto;
}

int32 symbolic_statement_update(int32 x) {
    requires x < 2147483647;
    ensures result == x + 1 by auto;
}
```

```expect
pass
```
