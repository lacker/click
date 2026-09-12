# A cell no loop binder owns is not joined, it is named

The loop's exits are described through the loop's declared binders: a cell the
exits wrote differently is a cell folded into one of them, and a proof after
the loop reads it back through that binder's model. This loop declares plain
memory and no binder at all, so there is nothing to read the differing cell
through, and the join refuses naming the block rather than replacing the cell
with a name no claim can explain.

```c filename=set_either.c
void set_either(int32* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            p[0] = 0;
            break;
        } else {
            p[0] = 1;
            break;
        }
    }
}
```

```click
verifying "set_either.c";

void set_either(int32* p, int32 flag) {
    owns p[0..1];
    ensures p[0] == 0 or p[0] == 1;
} by {
    loop {
        owns p[0..1];

        preserve by {
            if flag == 0 {
                step();
                step();
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
fail: the cell in `arg-memory` that the exits write differently is owned by no loop binder
```
