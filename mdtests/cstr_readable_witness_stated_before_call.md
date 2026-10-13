# Stating `strlen`'s readable-string precondition before the call

Lowering `strlen`'s precondition first emits one evaluator prerequisite: the
`size_t` length's range `bytes[0..len + 1u64]` fits an object, which the first
`have` states with a concrete witness. The next three `have`s carry the
caller's byte facts to the call: the viewable range, the nonterminating
prefix, and the definedness of each byte through the terminator. The final
`have` states the complete readable-string fact with the concrete witness. The
call step can therefore use only checked, retained facts instead of searching
the ambient context.

The caller holds only concrete byte facts, not `cstr_readable` itself, and
the terminator is not the first byte, so the `have` is the route to the
precondition.

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
    requires viewable(bytes[0..3]);
    requires bytes[0] != '\0';
    requires bytes[1] != '\0';
    requires bytes[2] == '\0';

    ensures result < 18446744073709551615u64 by {
        execute_until(statement(1));
        have exists (len: uint64) { len + 1u64 <= 9223372036854775807u64 } by {
            witness { len: 2u64 };
            simp();
        }
        have viewable(bytes[0..2u64 + 1u64]) by {
            transport(
                at(function.entry, viewable(bytes[0..3])),
                viewable(bytes[0..2u64 + 1u64])
            ) using {
                at(function.entry, viewable(bytes[0..3]));
            }
        }
        have forall (k: uint64) { k < 2u64 implies bytes[k] != '\0' } by {
            enumerate();
        }
        have forall (k: uint64) { k < 2u64 + 1u64 implies defined(bytes[k]) } by {
            intro();
            intro();
            transport(
                at(function.entry, viewable(bytes[0..3])),
                defined(bytes[k])
            ) using {
                k < 2u64 + 1u64;
                at(function.entry, viewable(bytes[0..3]));
            }
        }
        have exists (len: uint64) {
            len < 18446744073709551615u64 and
                viewable(bytes[0..len + 1u64]) and
                forall (k: uint64) { k < len implies bytes[k] != '\0' } and
                bytes[len] == '\0' and
                forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
        } by {
            witness { len: 2u64 };
            simp();
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
