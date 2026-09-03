# Local declaration lists

C0 accepts same-type local declaration lists and lowers each declarator in
source order.

```c filename=local_declaration_list.c
int32 local_declaration_list() {
    int32 i = 0, j = 1, k = 2;
    return i + j + k;
}
```

```click
verifying "local_declaration_list.c";

int32 local_declaration_list() {
    ensures result == 3 by auto;
}
```

```expect
pass
```
