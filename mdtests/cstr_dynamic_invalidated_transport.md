# An intervening write invalidates a dynamic loadability transport

```c filename=cstr_dynamic_invalidated_transport.c
int32 read_terminator(uint8 bytes[], int32 known_len) {
    int32 length;
    bytes[0] = bytes[0];
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_invalidated_transport.c";

int32 read_terminator(uint8 bytes[], int32 known_len) {
    requires input: cstr_readable(bytes);
    requires input_len: cstr_readable_len(bytes, known_len);
    requires 0 <= known_len;
    requires known_len < 2147483647;
    requires loadable(bytes[0..known_len + 1]);
    owns bytes[0..known_len + 1];
    ensures result >= 0 by {
        unfold(cstr_readable);
        unfold(cstr_readable_len);
        step();
        have exists (len: int32) {
            0 <= len and
                loadable(bytes[0..len + 1]) and
                forall (k: int32) {
                    0 <= k and k < len implies bytes[k] != '\0'
                } and
                bytes[len] == '\0'
        } by {
            witness(len = known_len);
            both {
                simp();
            } and {
                both {
                    both {
                        both {
                            transport(
                                at(function.entry, loadable(bytes[0..known_len + 1])),
                                loadable(bytes[0..known_len + 1])
                            ) using {
                                at(function.entry, loadable(bytes[0..known_len + 1]));
                            }
                        } and {
                            simp();
                        }
                    } and {
                        simp();
                    }
                } and {
                    simp();
                }
            }
        }
    }
}
```

```expect
fail: missing prerequisite (strlen precondition)
```
