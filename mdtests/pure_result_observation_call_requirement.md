# Exact observations preserve pure result call requirements

```c filename=call.c
int take(unsigned int a);
int native_call(void) { return take(123u); }
int take_native(unsigned int a);
int native_comparison(void) { return take_native(123u); }
```

```click
import click::c::stdio;
verifying "call.c";
extern int32 take(uint32 a) {
    requires to_integer(click::c::stdio::decimal_length(a as uint64)) <= 2147483647;
    ensures result == 0;
}
int32 native_call() {
    ensures result == 0;
}
extern int32 take_native(uint32 a) {
    requires click::c::stdio::decimal_length(a as uint64) <= 2147483647u64;
    ensures result == 0;
}
int32 native_comparison() {
    ensures result == 0;
}
```

```expect
pass
```
