# a call may not take ownership of string-literal storage

Modifying a string literal is undefined (C11 6.4.5p7), and a direct store into
one is rejected where it executes. A modular call performs its writes
abstractly through the memory it owns instead, so the same check belongs
at the call: otherwise passing literal storage to a callee that owns it stores
there, and the caller reads the stored value back.

C0 models a literal as an ordinary `uint8*`, so no qualifier catches this the
way `const` catches a write through a pointer-to-const.

```c filename=string_literal_mutable_footprint_rejected.c
void overwrite(uint8* p) {
    p[0] = 1;
}

int32 string_literal_mutable_footprint_rejected() {
    uint8* message = "ab";
    overwrite(message);
    return message[0];
}
```

```click
verifying "string_literal_mutable_footprint_rejected.c";

void overwrite(uint8* p) {
    owns p[0..1];
    ensures p[0] == 1;
} by { execute(); simp(); }

int32 string_literal_mutable_footprint_rejected() {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: mutable footprint covers read-only storage
```
