# Condition premises are found in whatever order they were stated

A smart derivation selects the condition facts connected to its goal through
shared values. The chain below is stated last link first, beside facts about
unrelated values; the derivation still finds every link.

```c filename=chain.c
int32 chain(int32 a, int32 b, int32 c, int32 d, int32 p, int32 q) {
    return a;
}
```

```click
verifying "chain.c";

theorem reversed_chain(a: int32, b: int32, c: int32, d: int32, p: int32, q: int32) {
    requires p < 7;
    requires c < d;
    requires q < 9;
    requires b < c;
    requires a < b;
    ensures a < d by close();
}
```

```expect
pass
```
