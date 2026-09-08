# Field values cannot be assumed from a declaration

Body expressions cannot yet bind or constrain a declared field. This must be
an explicit unsupported operation, not an unbound C variable or a silently
accepted relation to an unspecified model.

```click
resource cell(p: int32*) {
    field revision: int32;
    owns p[0..1];
    fact revision == p[0];
}
```

```expect
fail: resource `cell` field `revision` cannot be used in body expressions yet; field establishment is not supported
```
