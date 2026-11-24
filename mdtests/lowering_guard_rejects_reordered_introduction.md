# Reordering introductions cannot repair an undefined quantified claim

This variant also evaluates `k + 1` at `INT32_MAX`. It fails its domain
obligation before any citation or introduction can hide that requirement.

```click
theorem guarded_universal_reordered() {
    ensures forall (k: int32) {
        to_integer(k + 1) > 0 and k >= 0 implies k >= 0
    } by {
        intro();
        intro();
        have k >= 0;
        intro();
        close();
    }
}
```

```expect
fail: not established: `forall
```
