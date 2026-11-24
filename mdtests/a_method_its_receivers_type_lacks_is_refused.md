# A method its receiver's type lacks is refused

A method is resolved by its receiver's type, so one the type does not have
is refused with the type and the method's name, not read as a C field.

```click
import click::rust::slice;

theorem no_such_method(s: Slice<uint8>) {
    ensures s.size() == slice::len(s) by {
        close();
    }
}
```

```expect
fail: `Slice<uint8>` has no method `size`
```
