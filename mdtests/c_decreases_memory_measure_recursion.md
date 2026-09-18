# a C recursion measure may read memory

`drain` takes the same pointer on every call, so no parameter of it descends:
what descends is the cell the pointer names. The measure is a pure function of
that cell, and the kernel reads it twice — once in the memory `drain` enters
with, giving the value the recursion starts from, and once in the memory at
the recursive call, after the body has written the cell.

The two readings are of one declared expression at two states, exactly as a
loop's ranking members are, so the proof names the entry reading with `old`.

```c filename=c_decreases_memory_measure_recursion.c
int32 drain(int32 box[4]) {
    int32 result;
    if (box[0] > 0) {
        box[0] = box[0] - 1;
        result = drain(box);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_memory_measure_recursion.c";

function head(a: int32[]) -> int32 {
    a[0]
}

int32 drain(int32 box[4]) {
    decreases head(box);
    owns box[0..4];
    requires box[0] >= 0;
    ensures result == 0;
} by {
    step();
    branch {
        then {
            step();
            have 0 <= head(box) by { unfold(head(box)); simp(); }
            have head(box) < old(head(box)) by {
                unfold(head(box));
                simp();
            }
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    simp();
}
```

```expect
pass
```
