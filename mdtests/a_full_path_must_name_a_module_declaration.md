# a full library path must name a declaration of its module

`click::list::reverse` names a module that exists but a declaration it
does not have, so the path is refused rather than read as something else.

```click
theorem reverse_nil() {
    ensures click::list::reverse(List<int32>::Nil) == List<int32>::Nil by close();
}
```

```expect
fail: `click::list::reverse` names no declaration of Click library module `click::list`
```
