# A narrow cast does not establish a false value

```click
theorem wrong() {
    ensures 65521 as uint16 == 0 as uint16 by close();
}
```

```expect
fail: it is false at this point
```
