# Signed observations of a narrowed length have printable arithmetic certificates

The low word is an opaque signed value. Its explicit bounds support arithmetic;
none of these facts imply a bound on the original native-width length. MemoryState
operands retain their selectors after the source local changes.

```c filename=signed_narrowed_length_arithmetic.c
int32 distance(uint64 n, int32 remaining) {
    remaining = remaining - 1;
    return remaining;
}
```

```click
verifying "signed_narrowed_length_arithmetic.c";
int32 distance(uint64 n, int32 remaining) {
    requires 0 < remaining;
    requires remaining <= n as uint32 as int32;
    requires 0 <= n as uint32 as int32;
    requires 1000 >= n as uint32 as int32;
    ensures to_integer((n as uint32 as int32 - result - 1)) < to_integer(n as uint32 as int32);
} by {
    step();
    have to_integer((n as uint32 as int32 - remaining - 1)) < to_integer(n as uint32 as int32) by {
        solve() using {
            at(region(0).entry, 0 < remaining);
            at(region(0).entry, remaining <= n as uint32 as int32);
            0 <= n as uint32 as int32;
            1000 >= n as uint32 as int32;
        };
    }
    have 1000 >= to_integer((n as uint32 as int32 - remaining - 1)) by {
        solve() using {
            at(region(0).entry, 0 < remaining);
            at(region(0).entry, remaining <= n as uint32 as int32);
            0 <= n as uint32 as int32; 1000 >= n as uint32 as int32;
        };
    }
}
```

```expect
pass
```
