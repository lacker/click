# An imported theorem shadows a bare library theorem

The imported module declares its own `multiply_add`, which proves
only `a == a`. A bare citation names it, as a local theorem of the name
is named, so the library theorem `integer::multiply_add` does not close
this goal.
Before, a local theorem shadowed the library's while an imported one did not:
the citation silently applied the library theorem.

```click checked-only
import "an_imported_theorem_shadows_a_bare_library_theorem_module.click";
import click::integer;

theorem uses(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        apply(multiply_add(a, b, c));
        close();
    }
}
```

```expect
fail: `known` requires the current goal as an available semantic fact
```
