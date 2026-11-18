# Dynamic chosen witness rejects a proof with transport removed

```c filename=cstr_dynamic_choose_extract_missing_transport.c
uint64 read_terminator(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_choose_extract_missing_transport.c";

uint64 read_terminator(uint8 bytes[]) {
    requires click::c::string::readable(bytes);
    ensures result < 18446744073709551615u64 by {
        unfold(click::c::string::readable(bytes));
        step_until(region(1));
        have exists (len: uint64) {
            len < 18446744073709551615u64 and
                viewable(bytes[0..len + 1u64]) and
                forall (k: uint64) { k < len implies bytes[k] != '\0' } and
                bytes[len] == '\0' and
                forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
        } by {
            let found_len = obtain(at(function.entry, exists (found_len: uint64) {
                found_len < 18446744073709551615u64 and
                    viewable(bytes[0..found_len + 1u64]) and
                    forall (k: uint64) { k < found_len implies bytes[k] != '\0' } and
                    bytes[found_len] == '\0' and
                    forall (k: uint64) { to_integer(k) < to_integer(found_len + 1u64) implies defined(bytes[k]) }
            }));
            witness(found_len);
            both {
                left => { solve(); }
                right => {
                    both {
                        left => {
                            both {
                                left => {
                                    both {
                                        left => {
                                            both {
                                                left => {
                                                    solve();
                                                }
                                                right => {
                                                    solve();
                                                }
                                            }
                                        }
                                        right => {
                                            solve();
                                        }
                                    }
                                }
                                right => {
                                    solve();
                                }
                            }
                        }
                        right => {
                            solve();
                        }
                    }
                }
            }
        }
    }
}
```

```expect
fail: 0 of 1 selected derivation premises have checked source spellings; 1 were omitted: at(function.entry, viewable(bytes[0..
```
