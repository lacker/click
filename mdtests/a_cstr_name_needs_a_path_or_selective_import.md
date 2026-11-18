# a cstr name needs a path or a selective import

After `import click::c::string;` a sidecar writes `string::readable`; the bare
`readable` is not in scope.

```click
import click::c::string;

theorem readable_by_bare_name(text: uint8[]) {
    requires readable(text);
    ensures 1 == 1;
}
```

```expect
fail: readable
```
