# A matched resource's quantified fact can be instantiated and refolded

A universal memory fact exposed from a field-bearing resource keeps the exact
checked identity associated with its constructor payload. After a same-value
store gives the covered cell a new load identity, the fact can be proved at
the current state and immediately used to fold the resource again.

```c filename=resource_match_quantified_fact_round_trip.c
struct buffer {
    int32* data;
};

int32 write_zero(struct buffer* buffer) {
    buffer->data[0] = 0;
    return 0;
}
```

```click
spec enum PrefixTag { End(int32) }

resource zero_prefix(buffer: struct buffer*) {
    field tag: PrefixTag;
    match tag {
        PrefixTag::End(end) => {
            owns buffer->data;
            owns buffer->data[0..end];
            fact end == 1;
            fact forall (k: int32) {
                0 <= k and k < end implies buffer->data[k] == 0
            };
        },
    }
}

verifying "resource_match_quantified_fact_round_trip.c";

int32 write_zero(struct buffer* buffer) {
    owns prefix: zero_prefix(buffer);
    ensures result == 0;
} by {
    match prefix.tag {
        PrefixTag::End(end) => {
            have 0 <= 0 by {
                normalize();
            }
            have 0 < end by {
                rewrite(end == 1);
                normalize();
            }
            have buffer->data[0] == 0 by {
                instantiate(forall (k: int32) {
                    0 <= k and k < end implies buffer->data[k] == 0
                }, 0) using {
                    0 <= 0;
                    0 < end;
                }
                assumption();
            }
            unfold(prefix);
            step();
            have buffer->data[0] == 0 by {
                normalize();
            }
            have forall (k: int32) {
                0 <= k and k < end implies buffer->data[k] == 0
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < end);
                have k < 1 by {
                    simp() using {
                        k < end;
                        end == 1;
                    }
                }
                have k == 0 by {
                    arithmetic() using {
                        0 <= k;
                        k < 1;
                    }
                }
                rewrite(k == 0);
                normalize();
            }
            let prefix = fold(zero_prefix(buffer), {
                tag: PrefixTag::End(end)
            });
            step();
            simp();
        },
    }
}
```

```expect
pass
```
