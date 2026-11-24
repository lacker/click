# Restricted solve discovers a single theorem application

The listed facts restrict hypotheses, while available verified theorems are
reasoning rules. All arguments below are determined by the conclusion.

```click
function shifted(x: Integer) -> Integer { x + 7 }

theorem shifted_bound(x: Integer) {
    requires 0 <= x;
    ensures 7 <= shifted(x) by { unfold(shifted(x)); close(); }
}

theorem use_bound(value: Integer) {
    requires 0 <= value;
    ensures 7 <= shifted(value) by {
        close() using { 0 <= value; };
    }
}
```

```expect
pass
```
