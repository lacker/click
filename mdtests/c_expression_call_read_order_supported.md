# Unaffected and explicitly sequenced expression calls remain supported

Call lowering still accepts sibling expressions that do not read mutable
runtime state. It also preserves source constructs that explicitly sequence a
call before a later read, including statement boundaries, the left operand of
`||`, and a conditional operator's condition.

```c filename=call_read_order_supported.c
static inline int set(int *p) { *p = 2; return 0; }
static inline int zero(void) { return 0; }
static inline int add(int left, int right) { return left + right; }
static inline int index_of(void) { return 0; }
static const int stable = 4;

int unaffected_operand(void) {
    int x = 1;
    return set(&x) + 1;
}

int unaffected_arguments(void) {
    int x = 1;
    return add(set(&x), 1);
}

int unaffected_const_read(void) {
    return stable + zero();
}

int unaffected_automatic_read(void) {
    int local = 5;
    return local + zero();
}

int unaffected_array_address(void) {
    int values[1];
    values[0] = 7;
    return values[index_of()];
}

int sequenced_statement(void) {
    int x = 1;
    int result = set(&x);
    return x + result;
}

int sequenced_or(void) {
    int x = 1;
    return set(&x) || x;
}

int sequenced_conditional(void) {
    int x = 1;
    return set(&x) ? 0 : x;
}
```

```click
verifying "call_read_order_supported.c";

int32 unaffected_operand() {
    ensures result == 1 by auto;
}

int32 unaffected_arguments() {
    ensures result == 1 by auto;
}

int32 unaffected_const_read() {
    ensures result == 4 by auto;
}

int32 unaffected_automatic_read() {
    ensures result == 5 by auto;
}

int32 unaffected_array_address() {
    ensures result == 7 by auto;
}

int32 sequenced_statement() {
    ensures result == 2 by auto;
}

int32 sequenced_or() {
    ensures result == 1 by auto;
}

int32 sequenced_conditional() {
    ensures result == 2 by auto;
}
```

```expect
pass
```
