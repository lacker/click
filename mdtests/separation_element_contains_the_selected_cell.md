# Explicit containment of a selected element

```click
import click::separation;
theorem signed(p: int32*, lo: int32, hi: int32, i: int32) {
    requires lo <= i;
    requires i < hi;
    ensures contains(memory(p[lo..hi]), memory(p[i])) by {
        apply(separation::contains_element(p, lo, hi, i));
        close();
    }
}
theorem wide(p: uint64*, lo: uint64, hi: uint64, i: uint64) {
    requires lo <= i;
    requires i < hi;
    ensures contains(memory(p[lo..hi]), memory(p[i])) by {
        apply(separation::contains_element(p, lo, hi, i));
        close();
    }
}
```

```expect
pass
```
