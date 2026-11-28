# Rebasing keeps the selected element interval

```click
import click::separation;

theorem rebase_narrow(p: int32*, lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo <= hi;
    ensures contains(memory(p[lo..hi]), memory((p + lo)[0..hi-lo])) by {
        apply(separation::contains_rebase(p, lo, hi));
        close();
    }
}

theorem rebase_wide(p: uint8*, lo: uint64, hi: uint64) {
    requires 0u64 <= lo;
    requires lo <= hi;
    requires lo <= 9223372036854775807u64;
    ensures contains(memory(p[lo..hi]), memory((p + lo)[0u64..hi-lo])) by {
        apply(separation::contains_rebase(p, lo, hi));
        close();
    }
}
```

```expect
pass
```
