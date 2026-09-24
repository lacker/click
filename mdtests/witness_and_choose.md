# Witness and existential elimination

```c filename=witness_and_choose.c
int32 witness_zero(int32 n) {
    return 0;
}
```

```c filename=choose_requirement.c
int32 choose_requirement(int32 x) {
    return x;
}
```

```click
verifying "witness_and_choose.c";
verifying "choose_requirement.c";

int32 witness_zero(int32 n) {
    requires 0 < n;
    ensures found_zero: (0..n).any(|k| { k == result }) by {
        execute();
        witness(k = 0);
        simp();
    }
}

int32 choose_requirement(int32 x) {
    requires exists (k: int32) { k == x };
    ensures found_again_first: exists (j: int32) { j == x } by {
        execute();
        let (k: int32) satisfy { k == x };
        witness(j = k);
        simp();
    }
    ensures found_again_second: exists (j: int32) { j == x } by {
        execute();
        let (k: int32) satisfy { k == x };
        witness(j = k);
        simp();
    }
}
```

```expect
pass
```
