# Ordinary quantified helper proofs inside contract refinement

```click
contract int32 Source(int32 x) {
    requires x >= 0;
    ensures result == x;
}

contract int32 Target(int32 x) {
    requires x >= 0;
    ensures result >= 0;
}

theorem lift(callback: int32 (*)(int32)) {
    requires Source(callback);
    ensures Target(callback) by {
        unfold(Source);
        unfold(Target);
        intro();
        have forall (k: int32) { k == x implies k >= 0 } by {
            intro();
            intro();
            rewrite(k == x);
            assumption();
        }
        have result == x implies result >= 0 by {
            intro();
            instantiate(forall (k: int32) { k == x implies k >= 0 }, result) using { result == x; }
            assumption();
        }
        simp();
    }
}
```

```expect
pass
```
