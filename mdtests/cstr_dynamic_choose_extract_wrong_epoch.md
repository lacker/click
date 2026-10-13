# Dynamic chosen witness rejects a transport from the wrong epoch

```c filename=cstr_dynamic_choose_extract_wrong_epoch.c
uint64 read_terminator(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_choose_extract_wrong_epoch.c";

uint64 read_terminator(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures result < 18446744073709551615u64 by {
        unfold(cstr_readable);
        execute_until(statement(1));
        have exists (len: uint64) {
            len < 18446744073709551615u64 and
                viewable(bytes[0..len + 1u64]) and
                forall (k: uint64) { k < len implies bytes[k] != '\0' } and
                bytes[len] == '\0' and
                forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
        } by {
            obtain (found_len: uint64) {
                at(function.entry,
                    found_len < 18446744073709551615u64 and
                    viewable(bytes[0..found_len + 1u64]) and
                    forall (k: uint64) { k < found_len implies bytes[k] != '\0' } and
                    bytes[found_len] == '\0' and
                    forall (k: uint64) { k < found_len + 1u64 implies defined(bytes[k]) })
            }
            witness { len: found_len };
            both {
                both {
                    both {
                        both {
                            simp();
                        } and {
                            transport(
                                at(function.entry, viewable(bytes[0..found_len + 1u64])),
                                viewable(bytes[0..found_len + 1u64])
                            ) using {
                                at(statement(1).entry, viewable(bytes[0..found_len + 1u64]));
                            }
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
        execute();
        simp();
    }
}
```

```expect
fail: `transport using` requires an exact premise
```
