# local specification imports

An entry file can use a pure declaration supplied by a local Click module.

```click
import "specification_imports_model.click";

theorem imported_function_is_available(x: int32) {
    ensures imported_identity(x) == x by auto;
}
```

```expect
pass
```
