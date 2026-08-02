# Witness and choose tactics

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
    requires has_k: exists (int32 k) { k == x };
    ensures found_again_by_index: exists (int32 j) { j == x } by {
        execute();
        choose(k from requirement 0);
        witness(j = k);
        simp();
    }
    ensures found_again_by_label: exists (int32 j) { j == x } by {
        execute();
        choose(k from requirement has_k);
        witness(j = k);
        simp();
    }
}
```

```expect
pass
```
