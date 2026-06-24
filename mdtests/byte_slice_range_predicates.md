# byte-slice range predicates

This checks byte-slice predicates that are useful before committing to a full
C-string abstraction. `bytes_contains` is existential for symbolic ranges, so
proof scripts can open it with `choose` after unfolding. `bytes_all_not_eq`
is universal and can be used as a finite range fact after unfolding.

```c filename=byte_slice_range_predicates.c
int32 byte_slice_range_predicates(uint8 p[], int32 n) {
    return 0;
}
```

```click
verifying "byte_slice_range_predicates.c";

int32 byte_slice_range_predicates(uint8 p[], int32 n) {
    requires valid_range(p[0..n]);
    requires valid_range(p[0..3]);
    requires has_x: bytes_contains(p, 0, n, 'x');
    requires no_y_in_prefix: bytes_all_not_eq(p, 0, 3, 'y');

    ensures opened_contains: bytes_contains(p, 0, n, 'x') by {
        symbolic_execute();
        unfold(bytes_contains);
        choose(found from requirement has_x);
        witness(k = found);
        simp();
        close();
    }

    ensures second_prefix_byte_is_not_y: p[1] != 'y' by {
        symbolic_execute();
        unfold(bytes_all_not_eq);
        simp();
        close();
    }
}
```

```expect
pass
```
