# A bounded opaque wide result can be returned as int

```c filename=call.c
unsigned long value(void);
int main(void) { return value(); }
```

```click
verifying "call.c";
extern unsigned long value() { ensures result == 41u64; }
int main() { ensures result == 41; } by { execute(); simp(); }
```

```expect
pass
```
