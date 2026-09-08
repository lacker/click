# Calls in short-circuit right operands remain unsupported

The original wide-static startup example is retained here without rewriting
its C. It is blocked by the separate short-circuit call lowering gap; see
`issues/short-circuit-operand-calls.md`.

```c filename=wide.c
static long low = -9223372036854775807L - 1;
static unsigned long high = 18446744073709551615UL;
static unsigned long zero;
long read_low(void) { return low; }
unsigned long read_high(void) { return high; }
int main(void) { return read_low() < 0 && read_high() > 4294967295UL && zero == 0; }
```

```click
verifying "wide.c" as wide;
long read_low() {
    owns &wide::low[0..1];
    ensures result == old(wide::low);
} by { execute(); simp(); }
unsigned long read_high() {
    owns &wide::high[0..1];
    ensures result == old(wide::high);
} by { execute(); simp(); }
int main() {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: calls in the short-circuit right operand are not supported
```
