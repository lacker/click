# A matched resource's dependent body clauses lower in declaration order

The later quantified facts may use the scalar bounds established earlier in
the same selected resource body. The source program needs no proof-only edits.

```c filename=resource.c
int32 unchanged(int32* occupied, int32 capacity) { return 0; }
```

```click
spec enum PrefixTag { End(int32) }
resource partition(occupied: int32*, capacity: int32) {
    field tag: PrefixTag;
    match tag {
        PrefixTag::End(prefix) => {
            owns occupied[0..capacity];
            fact 0 <= prefix;
            fact prefix <= capacity;
            fact forall (k: int32) {
                0 <= k and k < prefix implies occupied[k] == 1
            };
            fact forall (k: int32) {
                prefix <= k and k < capacity implies occupied[k] == 0
            };
        },
    }
}
verifying "resource.c";
int32 unchanged(int32* occupied, int32 capacity) {
    owns part: partition(occupied, capacity);
    requires 0 <= capacity;
    ensures result == 0;
} by {
    match part.tag {
        PrefixTag::End(prefix) => {
            have 0 <= prefix by { assumption(); }
            have prefix <= capacity by { assumption(); }
            have forall (k: int32) {
                0 <= k and k < prefix implies occupied[k] == 1
            } by { assumption(); }
            have forall (i: int32) {
                0 <= i and i < prefix implies occupied[i] == 1
            } by {
                intro();
                intro();
                extract(0 <= i);
                extract(i < prefix);
                instantiate(forall (k: int32) {
                    0 <= k and k < prefix implies occupied[k] == 1
                }, i) using {
                    0 <= i;
                    i < prefix;
                }
                assumption();
            }
            unfold(part);
            let part = fold(partition(occupied, capacity), {
                tag: PrefixTag::End(prefix)
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
