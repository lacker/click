# The implicit closer proves a word equality from an Integer fact

Specification arithmetic is Integer arithmetic, so the antecedent of
`i + 1 == 2 implies i == 1` is the Integer fact `to_integer(i) + 1 == 2`. Its
consequent `i == 1` compares two `int32` words with no sum or difference, the
shape the indexed native-reading route handles. That route reads native
facts, and the Integer fact is not one, so it misses. The implicit closer's last route
then proves the equality from its two bounds, `to_integer(i) <= 1` and
`1 <= to_integer(i)`, each by the solver, as it already does for an equality
over a sum.

`i + 1 == 1 implies i == 0` closed before the change because `solve` reads
`to_integer(i) + 1 == 1` as `i == 0`; `i + 1 == 2` has no such reading.

```c filename=word_equality.c
int r(int i) { return i + 1; }
```

```click
verifying "word_equality.c";

int32 r(int32 i) {
    requires 0 <= i and i < 4;
    ensures true;
} by {
    have i + 1 == 1 implies i == 0 by {
        intro();
        have i == 0;
        close();
    }
    have i + 1 == 2 implies i == 1 by {
        intro();
        have i == 1;
        close();
    }
}
```

```expect
pass
```
