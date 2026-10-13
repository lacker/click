# A false claim about a wrapped value is refused

Converting 300 to `unsigned char` gives 44, not 300: the conversion is
modulo 256 (`mdtests/uint8_conversion_wraps_modulo_256.md`), and claiming
the unconverted value is refused rather than proved.

```c filename=a_false_claim_about_a_wrapped_value_is_refused.c
int f(int x) { unsigned char y = x; return y; }
```

```click
verifying "a_false_claim_about_a_wrapped_value_is_refused.c";

int32 f(int32 x) {
    requires x == 300;
    ensures result == 300;
} by { execute(); simp(); }
```

```expect
fail: `ensures result == 300` failed
```
