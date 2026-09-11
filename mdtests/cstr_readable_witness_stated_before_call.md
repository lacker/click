# Stating `strlen`'s readable-string precondition before the call

`strlen` requires `cstr_readable`, an existential whose body needs a
definedness guard for `len + 1`. That guard belongs under the binder that
binds `len`, so the precondition is a proposition an ordinary proof can
state: the `have` below writes it out, names its witness, and proves the
guard as the conjunct it is. The call step then finds the stated fact.

The caller holds only concrete byte facts, not `cstr_readable` itself, and
the terminator is not the first byte, so the `have` is the route to the
precondition.

```c filename=cstr_readable_witness.c
int32 fixed_string_length(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_readable_witness.c";

int32 fixed_string_length(uint8 bytes[]) {
    requires loadable(bytes[0..3]);
    requires bytes[0] != '\0';
    requires bytes[1] != '\0';
    requires bytes[2] == '\0';

    ensures result >= 0 by {
        have exists (len: int32) {
            0 <= len and
                loadable(bytes[0..len + 1]) and
                forall (k: int32) {
                    0 <= k and k < len implies bytes[k] != '\0'
                } and
                bytes[len] == '\0'
        } by {
            witness(len = 2);
            both {
                simp();
            } and {
                both {
                    both {
                        both {
                            simp();
                        } and {
                            simp();
                        }
                    } and {
                        enumerate();
                    }
                } and {
                    simp();
                }
            }
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
