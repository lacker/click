# A contracted call and a different direct store cannot join

Both exits own the same cell, but their stored values differ. The helper has a
verified contract; its implementation remains unchanged.

```c filename=paint.c
struct node { int32 shade; };

void repaint(struct node* p) {
    int32 next = 0;
    p->shade = next;
}

void paint(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            repaint(p);
            break;
        } else {
            p->shade = 1;
            break;
        }
    }
}
```

```click
verifying "paint.c";

void repaint(struct node* p) {
    owns p->shade;
    ensures p->shade == 0;
}

void paint(struct node* p, int32 flag) {
    owns p->shade;
    ensures p->shade == 0;
} by {
    loop {
        decreases 0;
        owns p->shade;
        maintain by {
            if flag == 0 { step(); step(); step(); }
            else { step(); step(); step(); }
        }
    }
    step();
    close();
}
```

```expect
fail: loop exits reach different states
```
