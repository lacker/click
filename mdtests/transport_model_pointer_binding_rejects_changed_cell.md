# A model pointer binding does not preserve a changed cell

Resolving an equal proof pointer supplies no frame evidence for a cell
that the C loop actually writes. Both alias and source are explicitly cited.

```c filename=transport_loop_alias.c
int32 update(int32 *p) {
    while (1) { p[0] = 9; break; }
    return p[0];
}
```
```click
verifying "transport_loop_alias.c";
spec enum View { At(int32*) }
resource first(p: int32*) {
    field model: View;
    match model {
        View::At(alias) => {
            owns p[0..2];
            fact p == alias;
            fact p[0] == 7;
        },
    }
}
int32 update(int32* p) {
    owns state: first(p);
    ensures result == 7;
} by {
    match state.model {
        View::At(alias) => {
            loop {
                owns state: first(p);
                decreases 0;
                invariant state.model == old(state.model);
                invariant state.model == View::At(alias);
                initialize by close();
                maintain by {
                    unfold(state);
                    step();
                    have alias[0] == 7 by { close(); }
                    let state = fold(first(p), {model: View::At(alias)});
                    step();
                }
            }
            unfold(state); step_until(function.exit);
            let state = fold(first(p), {model: View::At(alias)});
            close();
        },
    }
}
```
```expect
fail: `solve` failed
```
