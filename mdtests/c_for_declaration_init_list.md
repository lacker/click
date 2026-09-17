# Multiple declarations in a `for` initializer

C0 accepts same-type, initialized declaration lists in a `for` initializer and
lowers them in source order, just like scalar assignment initializer lists.

```c filename=for_declaration_init_list.c
int32 for_declaration_init_list() {
    int32 total = 0;
    for (int32 i = 0, j = 3; i < 3; i++, j--) {
        total = total + j;
    }
    return total;
}
```

```click
verifying "for_declaration_init_list.c";

int32 for_declaration_init_list() {
    ensures result == 6 by auto;
}
```

```expect
pass
```
