# Equivalent comparisons within a compound conclusion

```click
function image(x: Integer) -> Integer { 0 }
theorem law(x: Integer, y: Integer) {
    requires x < y;
    ensures image(x) == image(y) and x < y by { unfold(image(x)); unfold(image(y)); close(); }
}
theorem test(a: Integer, b: Integer) {
    requires a < b;
    ensures image(b) == image(a) and b > a by { close() using { a < b; }; }
}
```
```expect
pass
```
