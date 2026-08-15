# abstract resource rejects a body

An abstract resource has no locally visible definition. A resource with a body
is an ordinary resource declaration and must omit `abstract`.

```click
abstract resource permit(key: int32) {
    fact key >= 0;
}
```

```expect
fail: an `abstract resource` cannot have a body
```
