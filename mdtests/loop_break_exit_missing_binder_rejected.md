# An exit that does not hold a declared binder is refused by name

The exit join describes the one post-loop state through the loop's declared
binders, so every exit has to hand one back: the rule rebinds `c` at each exit
by family and argument equality, whatever the body called it. This `break`
leaves with the instance still unfolded, so there is no `painted(p)` to rebind
there, and the loop is refused naming the binder and the exit rather than
exporting a successor one of its exits does not stand in.

```c filename=paint_one.c
struct node { int32 shade; };

void paint_one(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            p->shade = 0;
            break;
        } else {
            p->shade = 1;
            break;
        }
    }
}
```

```click
verifying "paint_one.c";

spec enum Color { Red, Black }

resource painted(p: struct node*) {
    field color: Color;
    match color {
        Color::Red => { owns p->shade; fact p->shade == 0; },
        Color::Black => { owns p->shade; fact p->shade == 1; },
    }
}

void paint_one(struct node* p, int32 flag) {
    owns c: painted(p);
    requires c.color == Color::Black;
    ensures c.color == Color::Red or c.color == Color::Black;
} by {
    loop {
        owns c: painted(p);
        invariant c.color == Color::Black;

        preserve by {
            unfold(c);
            if flag == 0 {
                step();
                step();
                let c = fold(painted(p), { color: Color::Red });
                step();
            } else {
                step();
                step();
                step();
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: at loop exit 2, loop binder `c` has no owned `painted` instance
```
