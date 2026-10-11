# An alias equality cannot identify neighboring bytes

Pointer rewriting preserves the byte offset of the selected read. The equality
for the iterator cursor supplies no equality between two input bytes.

```click
theorem wrong_byte(p: const uint8*, bytes: uint8[], n: uint64) {
 requires p == bytes + n;
 ensures to_integer((int32)p[0]) == to_integer((int32)(bytes + n)[1]) by {
  rewrite(p == bytes + n);
  normalize();
 }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
