# An introduced variable hides a parameter of its name

`intro()` introduces the goal's `y`, which hides the theorem's parameter `y`
until the proof ends; the parameter is `outer.y`. A `have` reads `y` as the
introduced variable and `outer.y` as the parameter. Before, `have y == 7`
matched the requirement `y == 7` by its spelling and read the parameter.

```click quick-solve
theorem t(y: int32) {
    requires y == 7;
    ensures forall (y: int32) { y == y } by {
        intro();
        have outer.y == 7;
        close();
    }
}
```

```expect
pass
```
