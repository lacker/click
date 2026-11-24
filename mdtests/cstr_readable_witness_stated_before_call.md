# Stating the facts of the string a `strlen` call assembles before the call

`strlen` views a `cstr_at` string. The caller owns the three bytes and
holds concrete facts about them, not a string, so the call gives the length
of the string it assembles from them, `{ n: 2u64 }`, and the call checks
the string's facts at the call. The caller's facts hold at entry, and the
local declaration before the call starts a new memory state, so the three
`have`s
restate them at the call in the string's own form: the nonterminating prefix,
the terminator, and the definedness of each byte through the terminator. The
call step can therefore use only checked, retained facts instead of searching
the ambient context. The readable bound explicitly observes the machine sum
`2u64 + 1u64`, as the string definition does; a mathematical `2 + 1`
retains a different expression even when both evaluate to three.

```c filename=cstr_readable_witness.c
uint64 fixed_string_length(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_readable_witness.c";

uint64 fixed_string_length(uint8 bytes[]) {
    owns bytes[0..3];
    requires bytes[0] != '\0';
    requires bytes[1] != '\0';
    requires bytes[2] == '\0';

    ensures result == 2u64;
} by {
    step_until(region(1).entry);
    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies bytes[k] != '\0' } by {
        enumerate();
    }
    have bytes[2u64] == '\0' by {
        close();
    }
    have forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(2u64 + 1u64) implies defined(bytes[k]) } by {
        enumerate();
    }
    step(strlen, { n: 2u64 });
}
```

```expect
pass
```
