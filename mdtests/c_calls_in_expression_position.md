# Calls in expression position lower to checked call statements

These unchanged C functions exercise calls as return values, conditions,
nested arguments, and array indexes. The parser lowers each call to the
existing checked call-assignment transition before the kernel sees it.

```c filename=call_expression_increment.c
int32 call_expression_increment(int32 value) {
    return 1;
}
```

```c filename=call_expression_return.c
int32 call_expression_return(int32 value) {
    return call_expression_increment(value) + 1;
}
```

```c filename=call_expression_nested.c
int32 call_expression_nested(int32 value) {
    return call_expression_increment(call_expression_increment(value));
}
```

```c filename=call_expression_condition.c
int32 call_expression_condition(int32 value) {
    if (call_expression_increment(value) > 0)
        return 1;
    return 0;
}
```

```c filename=call_expression_index_of.c
int32 call_expression_index_of() {
    return 0;
}
```

```c filename=call_expression_index.c
int32 call_expression_index() {
    int32 values[2];
    values[0] = 7;
    values[call_expression_index_of()] = 8;
    return values[0];
}
```

```click
verifying "call_expression_increment.c";
verifying "call_expression_return.c";
verifying "call_expression_nested.c";
verifying "call_expression_condition.c";
verifying "call_expression_index_of.c";
verifying "call_expression_index.c";

int32 call_expression_increment(int32 value) {
    ensures result == 1 by auto;
}

int32 call_expression_return(int32 value) {
    ensures result == 2 by auto;
}

int32 call_expression_nested(int32 value) {
    ensures result == 1 by auto;
}

int32 call_expression_condition(int32 value) {
    ensures result == 1 by auto;
}

int32 call_expression_index_of() {
    ensures result == 0 by auto;
}

int32 call_expression_index() {
    ensures result == 8 by auto;
}
```

```expect
pass
```
