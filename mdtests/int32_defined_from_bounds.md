# `int32` definedness from the operands' bounds is an explicit step

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=int32_defined_from_bounds.c
struct box {
    int v;
};

int sum(int a, int b) {
    return a + b;
}

int difference(int a, int b) {
    return a - b;
}

int sum_by_solve(int a, int b) {
    return a + b;
}

int difference_by_solve(int a, int b) {
    return a - b;
}

int sum_by_listed_solve(int a, int b) {
    return a + b;
}

int sum_by_arithmetic(int a, int b) {
    return a + b;
}

int bump(struct box* b) {
    return 1;
}

int caller(struct box* b) {
    int got;
    got = bump(b);
    return got;
}
```

```click
resource counted(b: struct box*) {
    field total: int32;
    owns *b;
}

verifying "int32_defined_from_bounds.c";

int32 sum(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures to_integer(result) == to_integer(a + b);
} by {
    have defined(a + b) by {
        close() using { a < 100; b == 1; };
    }
}

int32 difference(int32 a, int32 b) {
    requires -5 <= a;
    requires 0 <= b;
    requires not (b > 7);
    ensures to_integer(result) == to_integer(a - b);
} by {
    have defined(a - b) by {
        close() using { -5 <= a; 0 <= b; not (b > 7); };
    }
}

int32 sum_by_solve(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures to_integer(result) == to_integer(a + b);
} by {
    have defined(a + b) by {
        close();
    }
}

int32 difference_by_solve(int32 a, int32 b) {
    requires -5 <= a;
    requires 0 <= b;
    requires not (b > 7);
    ensures to_integer(result) == to_integer(a - b);
} by {
    have defined(a - b) by {
        close();
    }
}

int32 sum_by_listed_solve(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures to_integer(result) == to_integer(a + b);
} by {
    have defined(a + b) by {
        close() using {
            a < 100;
            b == 1;
        };
    }
}

int32 sum_by_arithmetic(int32 a, int32 b) {
    requires a < 100;
    requires b == 1;
    ensures to_integer(result) == to_integer(a + b);
} by {
    have defined(a + b) by {
        close() using {
            a < 100;
            b == 1;
        };
    }
}

int32 bump(struct box* b) {
    owns st: counted(b);
    requires st.total < 100;
    ensures result == 1 or result == 2;
    ensures to_integer(st.total) == to_integer(old(st.total) + result);
} by {
    let { total: n } = unfold(st);
    let st = fold(counted(b), { total: n + 1 });
}

int32 caller(struct box* b) {
    owns st: counted(b);
    requires st.total < 100;
    ensures result == 1 implies to_integer(st.total) == to_integer(old(st.total) + 1);
} by {
    step();
    step(bump, { st: st });
}
```

```expect
pass
```
