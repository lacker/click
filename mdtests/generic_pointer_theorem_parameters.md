# Generic pointer theorem parameters retain their element type

```click
import click::separation;

theorem pointer_identity<T>(p: T*) {
    ensures p == p by { close(); }
}

theorem nested<T>(p: T*, lo: int32, hi: int32, a: int32, b: int32) {
    requires lo <= a;
    requires a <= b;
    requires b <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[a..b])) by {
        apply(separation::contains_subrange(p, lo, hi, a, b));
        close();
    }
}

theorem integers(p: int32*, lo: int32, hi: int32, a: int32, b: int32) {
    requires lo <= a;
    requires a <= b;
    requires b <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[a..b])) by {
        apply(nested(p, lo, hi, a, b));
        close();
    }
}

theorem pointers(p: int32**) {
    ensures p == p by { apply(pointer_identity(p)); close(); }
}

theorem bytes(p: uint8*, lo: int32, hi: int32, a: int32, b: int32) {
    requires lo <= a;
    requires a <= b;
    requires b <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[a..b])) by {
        apply(nested(p, lo, hi, a, b));
        close();
    }
}
theorem wide(p: int64*, lo: int32, hi: int32, a: int32, b: int32) {
    requires lo <= a;
    requires a <= b;
    requires b <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[a..b])) by {
        apply(nested(p, lo, hi, a, b));
        close();
    }
}

theorem pointer_cells(p: int32**, lo: int32, hi: int32, a: int32, b: int32) {
    requires lo <= a;
    requires a <= b;
    requires b <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[a..b])) by {
        apply(nested(p, lo, hi, a, b));
        close();
    }
}

```

```expect
pass
```
