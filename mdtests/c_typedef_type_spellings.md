# C integer and struct typedefs are resolved before verification

Named typedefs can stand in for the modeled integer and struct-pointer types.

```c filename=c_typedef_type_spellings.c
struct record {
    int value;
    uint8_t tag;
};

typedef struct record record_t;
typedef int32_t index_t;

int read_record(record_t* record, index_t index) {
    return record->value + index;
}
```

```click
verifying "c_typedef_type_spellings.c";

int read_record(struct record* record, int32_t index) {
    views record->value;
    requires index == 2;
    requires record->value <= 2147483645;
    ensures result == record->value + index by auto;
}
```

```expect
pass
```
