# known computes fast leaves without searching

`close()` combines indexed facts with goal-local arithmetic, identity, and
constructor checks. Pure function calls still need an explicit unfold.

```click
spec enum Choice { Empty, Full(Integer) }
function twice(x: Integer) -> Integer { x + x }

theorem computed_leaves(x: Integer, y: Integer) {
    requires x < y;
    ensures true by close();
    ensures 1 + 1 == 2 by close();
    ensures x + 1 > x by close();
    ensures x + y - y == x by close();
    ensures x * 0 == 0 by close();
    ensures x < y and x + 1 > x by close();
    ensures y < x or x + 1 > x by close();
    ensures not(Choice::Empty == Choice::Full(x)) by close();
    ensures twice(x) == x + x by { unfold(twice(x)); close(); }
}

theorem native_identity(x: uint32, y: uint32) {
    ensures x + y == y + x by close();
    ensures x - x == 0u32 by close();
}
```

```expect
pass
```
