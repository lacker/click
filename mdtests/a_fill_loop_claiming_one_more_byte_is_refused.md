# A fill loop claiming one more byte is refused

The postcondition of `a_fill_loop_over_a_size_t_range_needs_no_bound.md`
with `k <= length` in place of `k < length`. `bytes[length]` is past the
range the function owns and nothing wrote it, so the claim is refused.

```c filename=a_fill_loop_claiming_one_more_byte_is_refused.c
void fill(unsigned char *bytes, unsigned long length, unsigned char value) {
    for (unsigned long i = 0; i < length; i++) {
        bytes[i] = value;
    }
}
```

```click
import click::integer;
import click::separation;

verifying "a_fill_loop_claiming_one_more_byte_is_refused.c";
void fill(uint8* bytes, uint64 length, uint8 value) {
    owns bytes[0..length];
    ensures forall (k: uint64) { k <= length implies bytes[k] == value };
} by {
    step_until(loop(0).entry);
    loop {
        decreases length - i;
        owns bytes[0..length];
        invariant i <= length;
        invariant forall (k: uint64) { k < i implies bytes[k] == value };
        maintain by {
            mark before;
            step();
            step();
            have i <= length;
            have forall (k: uint64) { k < i implies bytes[k] == value } by {
                intro();
                intro();
                if k < at(before, i) {
                    instantiate(forall (k: uint64) { k < at(before, i) implies at(before, bytes[k]) == at(before, value) }, k);
                    have at(before, i) != k by {
                        close() using { k < at(before, i); };
                    }
                    have at(before, separate(memory(bytes[i]), memory(bytes[k]))) by {
                        apply(separation::separate_elements(bytes, at(before, i), k));
                    }
                    have separate(loop(0).statement(0).footprint, memory(bytes[k])) by {
                        close();
                    }
                    have at(loop(0).statement(0).exit, bytes[k]) == at(before, bytes[k]) by {
                        preserve(memory(bytes[k]), loop(0).statement(0));
                    }
                    have bytes[k] == at(loop(0).statement(0).exit, bytes[k]) by { close(); }
                    have bytes[k] == at(before, bytes[k]) by {
                        close();
                    }
                    have bytes[k] == value by {
                        rewrite(bytes[k], at(before, bytes[k]));
                        close();
                    }
                    close();
                } else {
                    have k < at(before, i) + 1;
                    have k <= at(before, i) by {
                        close() using { k < at(before, i) + 1; };
                    }
                    have k == at(before, i);
                    rewrite(k, at(before, i));
                    close();
                }
            }
        }
    }
    step_until(function.exit);
    have at(loop(0).exit, i) == length;
    have forall (k: uint64) { k < length implies bytes[k] == value } by {
        intro();
        intro();
        have k < at(loop(0).exit, i) by {
            rewrite(at(loop(0).exit, i), length);
            close();
        }
        instantiate(forall (k: uint64) { k < at(loop(0).exit, i) implies at(loop(0).exit, bytes[k]) == at(loop(0).exit, value) }, k);
        close();
    }
    close();
    close();
}
```

```expect
fail: checked outcome `close` search did not retain a complete proof for `fill.ensures_0`
```
