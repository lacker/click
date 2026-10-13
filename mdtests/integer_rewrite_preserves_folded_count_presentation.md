# Integer rewriting preserves a constant-folded native count observation

The native count expression remains the checked value. Replacing its exact
signed observation by 16 folds the source bound to 4081; retaining that spelling
must use the same normalized Integer claim, without extra assumptions.

```click
function observed_batch_prefix(total: uint64, remaining: uint64) -> int32 {
 (int32)(uint32)(total - remaining)
}
theorem rewritten_bound(a: uint64, remaining: uint64) {
 requires observed_batch_prefix(16u64, remaining) == 16;
 requires to_integer(a) <= 1 + 255 * to_integer(16);
 ensures to_integer(a) <= 1 + 255 * to_integer(observed_batch_prefix(16u64, remaining)) by {
  rewrite(observed_batch_prefix(16u64, remaining) == 16);
  arithmetic() using { to_integer(a) <= 1 + 255 * to_integer(16); };
 }
}
```

```expect
pass
```
