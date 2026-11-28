# Tuples construct, project and compare

Tuples have Rust's syntax (`design/tuples.md`): types `(A, B)`, `(A,)` and
`()`, values `(a, b)`, projections `t.0`, destructuring `let (a, b) = t;`
and tuple match patterns. A projection of a constructed tuple is its
component, equality of two constructed tuples is componentwise, and a
proof `match` on a symbolic tuple names its components. Components may be
C scalars, `Integer` or tuples.

```click
function swap(p: (int32, int32)) -> (int32, int32) {
    (p.1, p.0)
}

function sum_parts(p: (Integer, Integer)) -> Integer {
    let (a, b) = p;
    a + b
}

function pick(p: (int32, uint8)) -> int32 {
    match p {
        (value, tag) => value,
    }
}

theorem construction_and_projection(x: int32, y: int32) {
    ensures (x, y).0 == x by close();
    ensures (x, y).1 == y by close();
}

theorem swap_twice(p: (int32, int32)) {
    ensures swap(swap(p)) == p by {
        unfold(swap(p));
        unfold(swap((p.1, p.0)));
        match p {
            (a, b) => {
                close();
            }
        }
    }
}

theorem equality_is_componentwise(x: int32, y: int32, u: int32, v: int32) {
    requires (x, y) == (u, v);
    ensures x == u by close();
    ensures y == v by close();
}

theorem nested(x: int32, y: int32, z: int32) {
    ensures ((x, y), z).0 == (x, y) by close();
    ensures ((x, y), z).0.1 == y by {
        have ((x, y), z).0 == (x, y) by close();
        rewrite(((x, y), z).0, (x, y));
        close();
    }
}

theorem singleton_and_unit(x: int32) {
    ensures (x,).0 == x by close();
    ensures () == () by close();
}

theorem destructured(m: Integer, n: Integer) {
    ensures sum_parts((m, n)) == m + n by {
        unfold(sum_parts((m, n)));
        close();
    }
}
```

```expect
pass
```
