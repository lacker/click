# A loop exit disjunction ignores a closed true conjunct

Both exits prove the colour disjunction for the resource they hold. The
black exit also proves the closed fact `true == true`. The successor can
split on the shared disjunction even when one exit has that extra premise.

```c filename=paint_or_leave.c
struct node { int32 shade; };

void paint(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            p->shade = 0;
            break;
        } else {
            break;
        }
    }
}
```

```click
verifying "paint_or_leave.c";

spec enum Color { Red, Black }

resource painted(p: struct node*) {
    field color: Color;
    match color {
        Color::Red => { owns p->shade; fact p->shade == 0; },
        Color::Black => { owns p->shade; fact p->shade == 1; },
    }
}

void paint(struct node* p, int32 flag) {
    owns c: painted(p);
    requires c.color == Color::Black;
    ensures c.color == Color::Red or c.color == Color::Black;
} by {
    loop {
        decreases 0;
        owns c: painted(p);
        invariant c.color == Color::Black;

        maintain by {
            if flag == 0 {
                unfold(c);
                step();
                step();
                let c = fold(painted(p), { color: Color::Red });
                have c.color == Color::Red or c.color == Color::Black by close();
                step();
            } else {
                unfold(c);
                step();
                let c = fold(painted(p), { color: Color::Black });
                have true == true by close();
                have c.color == Color::Red or c.color == Color::Black by close();
                step();
            }
        }
    }
    have c.color == Color::Red or c.color == Color::Black by {
        cases {
            c.color == Color::Red => { close(); }
            c.color == Color::Black => { close(); }
        }
    }
    step();
    close();
}
```

```expect
pass
```
