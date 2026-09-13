# composite resource accepts a current-view fact

This checks that a current view is enough to provide read authority for a
composite resource fact.

```click
resource bogus(flag: int32*) {
    views flag[0..1];
    fact flag[0] == 0;
}
```

```expect
pass
```
