# A different direct store does not join a later contracted call

Both exits own the same cell but leave it holding different values. The helper has a
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
            p->shade = 1;
            break;
        } else {
            repaint(p);
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
