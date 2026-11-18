# A C string cannot be folded at a wrong length

`cstr_at(p, len)`, the `click::c::string` library resource, states that byte
`len` is the first terminator. The bytes
determine that length, so a fold at any other length must fail. `mk` owns the
bytes of a string of length `n` and claims to produce `cstr_at(p, n + 1)`: byte
`n` is a terminator, so the body fact that the first `n + 1` bytes are nonzero
cannot be established.

```c filename=cstr_at_fold_refuses_a_wrong_length.c
int32 mk(const uint8 *p, uint64 n) { return 0; }
```

```click
import click::c::string;

verifying "cstr_at_fold_refuses_a_wrong_length.c";

int32 mk(const uint8* p, uint64 n) {
    consumes p[0..n + 2u64];
    requires n < 18446744073709551614u64;
    requires forall (k: uint64) { 0u64 <= k and k < n implies p[k] != '\0' };
    requires p[n] == '\0';
    requires forall (k: uint64) { 0u64 <= k and k < n + 2u64 implies defined(p[k]) };
    produces cstr_at(p, n + 1u64);
} by {
    step_until(function.exit);
    fold(cstr_at(p, n + 1u64));
}
```

```expect
fail: unproved obligation: `forall (k: uint64) { 0u64 <= k and k < (n + 1u64) implies p[k] != 0u8 }`
```
