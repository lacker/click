# Stating `strlen`'s readable-string precondition before the call

Lowering `strlen`'s precondition first emits three evaluator prerequisites:
the bounded length, the viewability of each preceding byte, and the
viewability of the terminator. The first three `have`s state those exact
propositions with a zero witness. The final `have` states the complete
readable-string fact with the concrete witness. The call step can therefore
use only checked, retained facts instead of searching the ambient context.

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
    requires viewable(bytes[0..3]);
    requires bytes[0] != '\0';
    requires bytes[1] != '\0';
    requires bytes[2] == '\0';

    ensures result >= 0 by {
        execute_until(statement(1));
        have exists (len: int32) {
            0 <= len + 1
        } by {
            witness(len = 0);
            both {
                simp();
            } and {
                simp();
            }
        }
        have exists (len: int32) {
            defined(len + 1) and
                forall (k: int32) {
                    0 <= k and k < len implies viewable((bytes + k)[0..1])
                }
        } by {
            witness(len = 0);
            both {
                simp();
            } and {
                enumerate();
            }
        }
        have exists (len: int32) {
            defined(len + 1) and viewable((bytes + len)[0..1])
        } by {
            witness(len = 0);
            both {
                simp();
            } and {
                transport(
                    at(function.entry, viewable(bytes[0..3])),
                    viewable((bytes + 0)[0..1])
                ) using {
                    at(function.entry, viewable(bytes[0..3]));
                }
            }
        }
        have exists (len: int32) {
            0 <= len and
                viewable(bytes[0..len + 1]) and
                forall (k: int32) {
                    0 <= k and k < len implies bytes[k] != '\0'
                } and
                bytes[len] == '\0'
        } by {
            witness(len = 2);
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
