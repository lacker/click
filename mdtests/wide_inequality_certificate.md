# Smart 64-bit inequality expands to a simple certificate

The masked word is not nonzero for every input.  The equality premise records
the actual set-bit fact that makes the inequality true; smart reasoning must
turn that derivation into an explicit 64-bit rewrite followed by context-free
normalization.

```click
theorem set_low_bit_is_nonzero(word: uint64) {
    requires (word & 1u64) == 1u64;

    ensures (word & 1u64) != 0u64 by {
        simp();
    }
}
```

```expect
pass
```
