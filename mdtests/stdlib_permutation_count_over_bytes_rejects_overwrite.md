# Generic `permutation::count` refuses a byte overwrite as a permutation

For the input `[0, 1]`, copying the second byte over the first changes the
number of zero bytes from one to zero. The proof computes both counts before
trying to equate them, which is required by the byte-permutation claim.

```c filename=stdlib_permutation_count_over_bytes_rejects_overwrite.c
int32 duplicate_byte(uint8 p[2]) {
    p[0] = p[1];
    return 0;
}
```

```click
import click::permutation;

verifying "stdlib_permutation_count_over_bytes_rejects_overwrite.c";

predicate byte_permutation(a: uint8[], b: uint8[], lo: int32, hi: int32) {
    forall (x: uint8) {
        permutation::count(a, lo, hi, x) == permutation::count(b, lo, hi, x)
    }
}

int32 duplicate_byte(uint8 p[2]) {
    consumes p[0..2];
    requires p[0] == 0;
    requires p[1] == 1;
    ensures pair_permutation: byte_permutation(p, old(p), 0, 2);
} by {
    step();
    have p[0] == 1 by close();
    have p[1] == 1 by close();
    have permutation::count(p, 0, 2, 0u8) == 0 by close();
    have permutation::count(old(p), 0, 2, 0u8) == 1 by close();
    step();
    have byte_permutation(p, old(p), 0, 2) by {
        unfold(byte_permutation(p, old(p), 0, 2));
        intro();
        if x == 0u8 {
            rewrite(x, 0u8);
            rewrite(permutation::count(p, 0, 2, 0u8), 0);
            rewrite(permutation::count(old(p), 0, 2, 0u8), 1);
            normalize();
        } else {
            close();
        }
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
