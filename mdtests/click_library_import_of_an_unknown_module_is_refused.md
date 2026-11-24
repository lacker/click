# an import of an unknown Click library module is refused

The negative twin of [`click_library_import.md`](click_library_import.md).
`click::strings` names no `library/` module, so the import is refused at its
own position and the message lists the modules that exist.

```click
import click::strings;

theorem unused(x: int32) {
    ensures x == x by close();
}
```

```expect
fail: unknown Click library module `click::strings`; the library has click::separation, click::primitives, click::nat
```
