# `arithmetic using` closes a singleton range under a binder

A half-open range of width one contains exactly its lower bound. Under three
`intro()` steps the goal is an equality reached by combining one listed bound
with a listed strict bound through a machine successor.

```click
theorem singleton(lo: int32) {
    requires lo < 1000;
    ensures forall (k: int32) { lo <= k and k < lo + 1 implies k == lo } by {
        intro();
        intro();
        intro();
        arithmetic() using {
            lo <= k;
            k < lo + 1;
        }
    }
}
```

```expect
pass
```
