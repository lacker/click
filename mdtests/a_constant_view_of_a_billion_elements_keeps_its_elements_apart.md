# a constant view of a billion elements keeps its elements apart

The negative twin of
[`a_constant_view_of_a_billion_elements_verifies_promptly.md`](a_constant_view_of_a_billion_elements_verifies_promptly.md).
The elements of a seeded range are one run, but each element is its own cell
holding its own load: `a[0]` and `a[1]` are two values the contract says
nothing about, so claiming them equal is refused.

```c filename=a_constant_view_of_a_billion_elements_keeps_its_elements_apart.c
int32 first(int32 *a) { return a[0]; }
```

```click
verifying "a_constant_view_of_a_billion_elements_keeps_its_elements_apart.c";

int32 first(int32 *a) {
    views a[0..1000000000];
    ensures a[0] == a[1];
} by {
    execute();
    simp();
}
```

```expect
fail: a[0] == a[1]
```
