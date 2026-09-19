# arithmetic eliminates the listed Integer equalities

Any number of listed `Integer` equalities may take part in one `arithmetic()`
step. They are eliminated, in the order they are written, each solved for the
smallest atom it still mentions; the goal is then decided against what is left.
Nothing is searched: the two-premise combination limit applies to the
inequalities that survive elimination, not to the equalities.

The first theorem chains three equalities, which no pair of them proves. The
second eliminates one equality from an order goal and from both listed bounds,
leaving the ordinary two-inequality sum.

```click
theorem chained_integer_equalities(t: Integer, a: Integer, b: Integer, x: Integer, y: Integer) {
    requires t == a + x;
    requires a == b;
    requires x == y;
    ensures t == b + y by {
        arithmetic() using {
            t == a + x;
            a == b;
            x == y;
        }
    }
}

theorem bounded_integer_sum(t: Integer, a: Integer, b: Integer, x: Integer, y: Integer) {
    requires t == a + x;
    requires a <= b;
    requires x <= y;
    ensures t <= b + y by {
        arithmetic() using {
            t == a + x;
            a <= b;
            x <= y;
        }
    }
}
```

```expect
pass
```
