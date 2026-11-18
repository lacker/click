# `snprintf` with a literal format states each character it writes

A call to `snprintf` whose format is a string literal calls a function with
one parameter per conversion. Its contract is written from the format: the
result is the number of characters the format produces, and each character
within the first `size - 1` is stated with the decimal rendering functions of
`click::c::stdio`. `decimal_length_n` gives an `n`-digit value's length,
`decimal_digit_of_length` a digit, and `pow10_e` a power of ten.

`".%03u"` is the fraction `string_get_size` in Linux `lib/string_helpers.c`
writes: a `.` and three digits, zero-padded.

```c filename=snprintf_digits.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int render(char *buf, unsigned int n)
{
	return snprintf(buf, 8, "%u", n);
}

int fraction(char *tmp, unsigned int remainder)
{
	return snprintf(tmp, 12, ".%03u", remainder);
}
```

```click
import click::c::stdio;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "snprintf_digits.c";

int32 render(char buf[], uint32 n) {
    requires n == 42u32;
    owns buf[0..8];
    ensures result == 2 by {
        step_until(function.exit);
        have stdio::decimal_length(42u64) == 2u64 by {
            apply(stdio::decimal_length_2(42u64));
        }
        have result == 2 by {
            solve() using { result == stdio::decimal_length(n as uint64) as int32; n == 42u32; stdio::decimal_length(42u64) == 2u64; };
        }
    }
    ensures buf[0] == 52 by {
        step_until(function.exit);
        have n as uint64 == 42u64 by { solve(); }
        have stdio::decimal_length(n as uint64) == 2u64 by {
            rewrite(n as uint64, 42u64);
            apply(stdio::decimal_length_2(42u64));
        }
        have stdio::decimal_digit(n as uint64, 0u64) == 52u8 by {
            rewrite(n as uint64, 42u64);
            apply(stdio::pow10_1());
            apply(stdio::decimal_digit_of_length(42u64, 2u64, 0u64));
            solve() using {
                stdio::decimal_digit(42u64, 0u64) == (48u64 + 42u64 / stdio::pow10(2u64 - 1u64 - 0u64) % 10u64) as uint8;
                stdio::pow10(1u64) == 10u64;
            };
        }
        have buf[0] == stdio::decimal_digit(n as uint64, 0u64) by {
            have 0u64 < stdio::decimal_length(n as uint64) and 0u64 + 1u64 < 8u64;
            instantiate(forall (k: uint64) {
                k < stdio::decimal_length(n as uint64) and k + 1u64 < 8u64 implies buf[k] == stdio::decimal_digit(n as uint64, k)
            }, 0u64);
            solve();
        }
        have buf[0] == 52 by {
            solve() using { buf[0] == stdio::decimal_digit(n as uint64, 0u64); stdio::decimal_digit(n as uint64, 0u64) == 52u8; };
        }
    }
}

int32 fraction(char tmp[], uint32 remainder) {
    requires remainder == 5u32;
    owns tmp[0..12];
    ensures result == 4 by {
        step_until(function.exit);
        have remainder as uint64 == 5u64 by { solve(); }
        have stdio::decimal_length(5u64) == 1u64 by {
            apply(stdio::decimal_length_1(5u64));
        }
        have stdio::padded_length(remainder as uint64, 3u64) == 3u64 by {
            rewrite(remainder as uint64, 5u64);
            unfold(stdio::padded_length(5u64, 3u64));
            solve() using { stdio::decimal_length(5u64) == 1u64; };
        }
        have result == 4 by {
            solve() using {
                result == (1u64 + stdio::padded_length(remainder as uint64, 3u64)) as int32;
                stdio::padded_length(remainder as uint64, 3u64) == 3u64;
            };
        }
    }
    ensures tmp[0] == 46;
}
```

```expect
pass
```
