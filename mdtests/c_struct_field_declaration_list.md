# C struct field declaration lists

Same-type struct fields can share one declaration while retaining their
source-order ABI layout.

```c filename=struct_field_declaration_list.c
struct pair {
    int32 first, second;
};

int32 struct_field_declaration_list(struct pair* value) {
    return value->first + value->second;
}
```

```click
verifying "struct_field_declaration_list.c";

int32 struct_field_declaration_list(struct pair* value) {
    views value->first;
    views value->second;
    requires value->first >= 0;
    requires value->first <= 100;
    requires value->second >= 0;
    requires value->second <= 100;
    ensures result == value->first + value->second by auto;
}
```

```expect
pass
```
