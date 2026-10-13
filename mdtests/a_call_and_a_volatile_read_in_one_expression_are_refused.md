# A call and a volatile read in one expression are refused

Reading a `volatile` object twice is itself observable, so Click does not
check both orders by rereading it; the expression stays refused.

```c filename=volatile_operand.c
volatile int g;
int one(void) { return 1; }
int f(void) { return one() + g; }
```

```click
verifying "volatile_operand.c";

int one() { ensures result == 1 by auto; }
int f() { ensures result >= 0 or result < 0; } by { execute(); simp(); }
```

```expect
fail: an expression call and a potentially aliased operand read are not supported
```
