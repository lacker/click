# Scalar bound rewriting requires equality evidence

```c filename=bounds.c
void anchor() {}
```

```click
verifying "bounds.c";
theorem reduced_bound(value: uint32, divisor: uint32) {
 requires value < divisor;
 ensures value < 65521u32 by {
  rewrite(65521u32, divisor);
  close();
 }
}
```

```expect
fail: exact available fact
```
