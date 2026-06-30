# uint8 pure function in a loop invariant

This checks that loop-invariant spec lowering preserves the element type for
pure Click functions over `uint8[]` array refs. The loop writes only the tail,
so the first byte remains equal to its entry-state value.

```c filename=uint8_loop_invariant_pure_function.c
uint8 fill_byte_tail(uint8 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = 'z';
        i = i + 1;
    }
    return p[0];
}
```

```click
verifying "uint8_loop_invariant_pure_function.c";

function first_byte(uint8 p[]) -> uint8 {
    p[0]
}

uint8 fill_byte_tail(uint8 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires valid_range(p[0..n]);
    requires write(p[0..n]);
    for loop(0) {
        invariant i >= 1 and i <= n by auto;
        invariant first_byte(p) == old(first_byte(p)) by auto;
    }
    ensures first_preserved: result == old(first_byte(p)) by auto;
}
```

```expect
pass
```
