# Every pure match arm must prove the goal

```click
spec enum Item { Empty, Value(int32) }
theorem false_case(item: Item) {
    ensures item == Item::Empty by {
        match item {
            Item::Empty => { close(); },
            Item::Value(value) => { normalize(); },
        }
    }
}
```
```expect
fail: `normalize` goal did not normalize to true
```
