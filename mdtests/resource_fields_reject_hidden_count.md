# Pure functions cannot hide counting a field-bearing resource

The function precedes the resource to check forward declaration resolution.

```click
function population(p: int32*) -> List<int32> {
    List::Cons(count(cell(p)), List::Nil)
}

resource cell(p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}
```

```expect
fail: resource `cell` has fields and is not countable
```
