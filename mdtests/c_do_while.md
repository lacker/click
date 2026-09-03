# Do-while loops

C0 lowers a post-tested `do ... while` loop to one initial body execution and
then the existing pre-tested `while` form.

```c filename=do_while.c
int32 do_while_count() {
    int32 i = 0;
    do {
        i++;
    } while (i < 3);
    return i;
}
```

```click
verifying "do_while.c";

int32 do_while_count() {
    ensures result == 3 by auto;
}
```

```expect
pass
```
