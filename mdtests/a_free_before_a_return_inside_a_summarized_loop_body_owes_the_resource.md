# a `free` before a `return` inside a summarized loop body owes the resource

`release_early` borrows `p`'s allocation and cell (`owns` returns them at
exit), but the path that returns from inside the loop frees them first. The
returned path is a function exit, so the exit rule finds nothing to return
and refuses it. Before returns were carried by the loop rule this verified:
the only certified path was the one that fell out of the loop with `p`
intact.

```c filename=a_free_before_a_return_inside_a_summarized_loop_body_owes_the_resource.c
int32 release_early(int32 *p, int32 n) {
    int32 i = 0;
    while (i < n) {
        if (i == 2) {
            free(p);
            return 0;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "a_free_before_a_return_inside_a_summarized_loop_body_owes_the_resource.c";

int32 release_early(int32 *p, int32 n) {
    requires n == 5;
    owns allocation(p, 4);
    owns p[0..1];
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        owns allocation(p, 4);
        owns p[0..1];
    }
    step();
    close();
}
```

```expect
fail: missing resource fact
```
