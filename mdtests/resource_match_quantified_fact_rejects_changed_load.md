# A changed covered load invalidates a matched quantified fact

Matching a folded resource publishes its selected arm's bounded universal
fact, but the fact remains tied to the memory state it describes. Writing a
different value into the covered interval invalidates that fact, so folding
the unchanged model back is rejected.

```c filename=resource_match_quantified_fact_rejects_changed_load.c
struct buffer {
    int32* data;
};

int32 write_one(struct buffer* buffer) {
    buffer->data[0] = 1;
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

verifying "resource_match_quantified_fact_rejects_changed_load.c";

int32 write_one(struct buffer* buffer) {
    owns prefix: zero_prefix(buffer);
    ensures result == 0;
} by {
    match prefix.tag {
        PrefixTag::End(end) => {
            have 0 <= 0 by {
                normalize();
            }
            have 0 < end by {
                rewrite(end, 1);
                normalize();
            }
            have buffer->data[0] == 0 by {
                instantiate(forall (k: int32) {
                    0 <= k and k < end implies buffer->data[k] == 0
                }, 0) using {
                    0 <= 0;
                    0 < end;
                };
                known();
            }
            unfold(prefix);
            step();
            let prefix = fold(zero_prefix(buffer), {
                tag: PrefixTag::End(end)
            });
            step();
            solve();
        },
    }
}
```

```expect
fail: unproved obligation: `forall (k: int32) { 0 <= k and k < (end as int32) implies (let read_pointer = buffer->data; read_pointer)[k] == 0 }`
```
