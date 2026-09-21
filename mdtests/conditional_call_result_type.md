# conditional expression temporaries keep their common type

Lowering a conditional expression into lazy branches must preserve the
conditional's C result type and its metadata. Previously the generated
temporary for a branch containing a call was declared `int32`, so wide
unsigned, wide signed, and pointer capacities could not flow through a
validated conditional. Now the temporary carries the conditional's own
common result type for supported arithmetic and pointer combinations, and
nested conditionals choose branch lazily, as for
`c_calls_in_conditional_branch.md`.

```c filename=conditional_call_wide.c
unsigned long wide(void) { return 4294967296UL; }
unsigned long zero(void) { return 0UL; }
unsigned long choose_ul(int32 flag) { return flag ? wide() : zero(); }
unsigned long choose_zero(int32 flag) { return flag ? zero() : wide(); }
int64 wide_i64(void) { return 2147483648L; }
int64 one_i64(void) { return 1L; }
int64 choose_i64(int32 flag) { return flag ? wide_i64() : one_i64(); }
int32* initiated(int32* p) { return p; }
int32* pick(int32* p, int32 flag, int32* q) { return flag ? initiated(p) : q; }
uint64 dispatch(uint64 (*what)(uint64), int32 flag) { return flag ? what(4294967296UL) : zero(); }
```

```click
verifying "conditional_call_wide.c";

unsigned long wide() {
    ensures result == 4294967296 by auto;
}
unsigned long zero() {
    ensures result == 0 by auto;
}
unsigned long choose_ul(int32 flag) {
    requires flag != 0;
    ensures result == 4294967296 by auto;
}
unsigned long choose_zero(int32 flag) {
    requires flag == 0;
    ensures result == 4294967296 by auto;
}
int64 wide_i64() {
    ensures result == 2147483648 by auto;
}
int64 one_i64() {
    ensures result == 1 by auto;
}
int64 choose_i64(int32 flag) {
    requires flag != 0;
    ensures result == 2147483648 by auto;
}
int32* initiated(int32* p) {
    ensures result == p;
}
int32* pick(int32* p, int32 flag, int32* q) {
    requires flag != 0;
    ensures result == p;
}
uint64 dispatch(uint64 (*what)(uint64), int32 flag) {
    requires flag != 0;
    requires Wide(what);
    ensures result == 4294967296 by { execute(); simp(); }
}
contract Wide() for uint64(uint64 seed) {
    ensures result == seed;
}
```

```expect
pass
```
