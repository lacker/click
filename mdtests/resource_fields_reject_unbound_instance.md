# Field metadata cannot be erased during resource transfer

Until resource instance binding and field establishment are implemented,
an ordinary resource call must not silently forget the declared fields.

```click
resource cell(p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}

int32 read_cell(int32* p) {
    consumes cell(p);
    produces cell(p);
}
```

```expect
fail: resource `cell` has fields; resource instance binding and field establishment are not supported yet
```
