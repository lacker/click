# affine resource rejects duplicate token clauses

This checks that an affine named resource is not silently duplicated by writing
the same resource requirement twice.

```c filename=use_once.c
int32 use_once(int32 cb) {
    return 0;
}
```

```click
affine resource can_complete(cb: int32);

verifying "use_once.c";

int32 use_once(int32 cb) {
    requires can_complete(cb);
    requires can_complete(cb);

    ensures result == 0 by auto;
}
```

```expect
fail: duplicate affine resource `can_complete(cb)`
```
