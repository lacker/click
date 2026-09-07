# generic function bodies retain their symbolic types

A type parameter is opaque inside a generic definition. An `int32` literal
cannot be returned where the declaration promises arbitrary `T`.

```click
function fabricated<T>(value: T) -> T {
    0
}
```

```expect
fail: function `fabricated` returns T, but its body has type int32
```
