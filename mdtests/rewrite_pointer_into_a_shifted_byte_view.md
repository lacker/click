# Rewrite a pointer into a shifted byte view

The shifted range keeps its endpoint expression `(i + 4) - i`. After
rewriting the model pointer, the goal names the same address and state
with a literal four-byte extent. The checked viewability comparison recognizes
that structural constant without changing the stored range or reading
unrelated facts.

```c filename=alias.c
void keep(const uint8* p, int32 n, int32 i) {}
```

```click
verifying "alias.c";

spec enum Link { Node(const uint8*) }
resource Cell(p: const uint8*, n: int32, i: int32) {
    field model: Link;
    match model {
        Link::Node(q) => {
            owns p[0..n];
            fact 0 <= i;
            fact to_integer(i) <= to_integer(i + 4);
            fact to_integer(i + 4) <= to_integer(n);
            fact q == p + i;
        },
    }
}

void keep(const uint8* p, int32 n, int32 i) {
    requires 0 <= n;
    requires n <= 22204;
    requires 0 <= i;
    requires i <= 22200;
    owns h: Cell(p, n, i);
} by {
    match h.model {
        Link::Node(q) => {
            unfold(h);
            have viewable(p[i..i + 4]) by {
                transport(viewable(p[0..n]), viewable(p[i..i + 4])) using {
                    viewable(p[0..n]);
                    0 <= i;
                    to_integer(i) <= to_integer(i + 4);
                    to_integer(i + 4) <= to_integer(n);
                };
            }
            have viewable(q[0..4]) by {
                rewrite(q, p + i);
                solve() using { viewable(p[i..i + 4]); };
            }
            let h = fold(Cell(p, n, i), { model: Link::Node(q) });
            step_until(function.exit);
            solve();
        },
    }
}
```

```expect
pass
```
