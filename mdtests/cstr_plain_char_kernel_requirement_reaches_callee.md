# Character C-string requirements reach kernel-target callees

The local declaration before the call leaves the bytes of `src` unchanged.
Carry the entry range's viewability and each byte's definedness across
that declaration, then use the entry length as the callee's witness.

```c filename=cstr_plain_char_kernel_requirement_reaches_callee.c
int check(const char *src) { return 0; }
int outer(const char *src) {
    int result = check(src);
    return result;
}
```

```click
import click::c::string;

target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "cstr_plain_char_kernel_requirement_reaches_callee.c";
int32 check(const char* src) {
    requires string::readable(src);
    ensures result == 0;
}
int32 outer(const char* src) {
    requires string::readable(src);
    ensures result == 0;
} by {
    unfold(string::readable(src));
    have entry_string: at(function.entry, exists (n: uint64) {
        n < 18446744073709551615u64 and
        viewable((src as (uint8 *))[0..n + 1u64]) and
        forall (k: uint64) { k < n implies (src as (uint8 *))[k] != '\0' } and
        (src as (uint8 *))[n] == '\0' and
        forall (k: uint64) { to_integer(k) < to_integer(n + 1u64) implies defined((src as (uint8 *))[k]) }
    }) by { known(); }
    step();
    let n = obtain(entry_string);
    have at(function.entry, viewable((src as (uint8 *))[0..n + 1u64])) by { known(); }
    have separate(region(0).footprint, memory((src as (uint8 *))[0..n + 1u64])) by {
        normalize() using {};
    }
    have viewable((src as (uint8 *))[0..n + 1u64]) by {
        preserve(memory((src as (uint8 *))[0..n + 1u64]), region(0));
    }
    have entry_defined: at(region(0).entry, forall (j: uint64) { to_integer(j) < to_integer(n + 1u64) implies defined((src as (uint8 *))[j]) }) by { known(); }
    have forall (j: uint64) { to_integer(j) < to_integer(n + 1u64) implies defined((src as (uint8 *))[j]) } by {
        intro(); intro();
        instantiate(entry_defined, j);
        have at(region(0).entry, defined((src as (uint8 *))[j])) by { known(); }
        have separate(region(0).footprint, memory((src as (uint8 *))[j])) by {
            have separate(memory(result), memory((src as (uint8 *))[j])) by { normalize(); }
            normalize() using { separate(memory(result), memory((src as (uint8 *))[j])); };
        }
        preserve(memory((src as (uint8 *))[j]), region(0));
    }

    have n < 18446744073709551615u64 by { known(); }
    have forall (k: uint64) { k < n implies (src as (uint8 *))[k] != '\0' } by { known(); }
    have (src as (uint8 *))[n] == '\0' by { known(); }
    step() by { witness(n); known(); }
}
```

```expect
pass
```
