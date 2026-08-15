# resource without body requires abstract

A resource declaration without a body introduces an abstract exact-match
resource. That abstraction must be explicit rather than inferred from a
semicolon.

```click
resource permit(key: int32);
```

```expect
fail: a resource without a body must be declared with `abstract resource`
```
