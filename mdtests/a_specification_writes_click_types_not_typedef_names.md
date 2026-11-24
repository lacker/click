# A specification writes Click's types, not typedef names

A typedef name of the verified source may restate a type in a function head.
A specification position writes Click's type, the same in every target
language, so a theorem parameter of a typedef type is refused.

```c filename=main.c
typedef unsigned int u32;

u32 twice(u32 n) {
    return n + n;
}
```

```click
verifying "main.c";

theorem small(n: u32) {
    requires n <= 1000u32;
    ensures n <= 1000u32 by close();
}
```

```expect
fail: unknown algebraic datatype `u32`
```
