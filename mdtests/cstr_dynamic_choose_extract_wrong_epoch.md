# Dynamic chosen witness rejects a transport from the wrong epoch

```c filename=cstr_dynamic_choose_extract_wrong_epoch.c
int32 read_terminator(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_choose_extract_wrong_epoch.c";

int32 read_terminator(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures result >= 0 by {
        unfold(cstr_readable);
        execute_until(statement(1));
        have exists (len: int32) {
            0 <= len and
                viewable(bytes[0..len + 1]) and
                forall (k: int32) {
                    0 <= k and k < len implies bytes[k] != '\0'
                } and
                bytes[len] == '\0' and
                forall (k: int32) { 0 <= k and k < len + 1 implies defined(bytes[k]) }
        } by {
            let (found_len: int32) satisfy {
                at(function.entry,
                    0 <= found_len and
                    viewable(bytes[0..found_len + 1]) and
                    forall (k: int32) {
                        0 <= k and k < found_len implies bytes[k] != '\0'
                    } and
                    bytes[found_len] == '\0' and
                    forall (k: int32) { 0 <= k and k < found_len + 1 implies defined(bytes[k]) })
            };
            witness(len = found_len);
            both {
                simp();
            } and {
                both {
                    both {
                        both {
                            both {
                                simp();
                            } and {
                                transport(
                                    at(function.entry, viewable(bytes[0..found_len + 1])),
                                    viewable(bytes[0..found_len + 1])
                                ) using {
                                    at(statement(1).entry, viewable(bytes[0..found_len + 1]));
                                }
                            }
                        } and {
                            simp();
                        }
                    } and {
                        simp();
                    }
                } and { simp(); }
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
