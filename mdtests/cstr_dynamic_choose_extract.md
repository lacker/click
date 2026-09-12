# Chosen C-string witness preserves an entry loadability citation

```c filename=cstr_dynamic_choose_extract.c
int32 read_terminator(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_choose_extract.c";

int32 read_terminator(uint8 bytes[]) {
    requires input: cstr_readable(bytes);
    ensures result >= 0 by {
        unfold(cstr_readable);
        execute_until(statement(1));
        have exists (len: int32) {
            0 <= len and
                loadable(bytes[0..len + 1]) and
                forall (k: int32) {
                    0 <= k and k < len implies bytes[k] != '\0'
                } and
                bytes[len] == '\0'
        } by {
            choose(found_len from requirement input);
            witness(len = found_len);
            both {
                simp();
            } and {
                both {
                    both {
                        both {
                            simp();
                        } and {
                            extract(at(function.entry, loadable(bytes[0..found_len + 1])));
                            transport(
                                at(function.entry, loadable(bytes[0..found_len + 1])),
                                loadable(bytes[0..found_len + 1])
                            ) using {
                                at(function.entry, loadable(bytes[0..found_len + 1]));
                            }
                        }
                    } and {
                        simp();
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
