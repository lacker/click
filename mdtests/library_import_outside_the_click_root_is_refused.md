# a library import outside the `click::` root is refused

Click library modules are rooted at `click`, so `import std::list;` cannot
mean the library's list module, or C++'s or Rust's `std`. A project file is
imported by a quoted path instead.

```click
import std::list;

theorem unused(x: int32) {
    ensures x == x by close();
}
```

```expect
fail: `import std::list;` names no Click library module
```
