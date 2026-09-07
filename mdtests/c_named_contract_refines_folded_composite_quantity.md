# Callback refinement frames a folded-composite quantity

Symbolic quantity refinement applies to nonrecursive folded composites as
opaque resources. It splits and recombines the population count without
opening the composite or inspecting its body.

```click
abstract resource atom();

resource bundle() {
    contains atom();
}

contract void PreserveUsedBundles(int32 available, int32 used) {
    requires 0 <= used;
    owns used of bundle();
}

contract void PreserveAvailableBundles(int32 available, int32 used) {
    requires 0 <= used and used <= available;
    owns available of bundle();
}

theorem preserving_used_bundles_preserves_available(
    callback: void (*)(int32, int32)
) {
    requires PreserveUsedBundles(callback);
    ensures PreserveAvailableBundles(callback) by {
        unfold(PreserveUsedBundles);
        unfold(PreserveAvailableBundles);
        simp();
    }
}
```

```expect
pass
```
