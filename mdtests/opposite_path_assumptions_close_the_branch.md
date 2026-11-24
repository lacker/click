# Opposite path assumptions close an impossible branch

Introducing the opposite of a held condition makes the nested context
inconsistent without changing the parent context. Both assumption orders
admit any goal in that impossible branch.

```click
theorem equality_then_inequality(x: int32, y: int32) {
    ensures x == y implies (x != y implies 0 == 1) by {
        intro();
        intro();
        close();
    }
}

theorem inequality_then_equality(x: int32, y: int32) {
    ensures x != y implies (x == y implies 0 == 1) by {
        intro();
        intro();
        close();
    }
}

theorem searched_contradictory_branch(x: int32, y: int32) {
    ensures x == y implies (x != y implies 0 == 1) by close();
}
```

```expect
pass
```
