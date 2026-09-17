# bounded loop verification

This checks the current bounded loop path: a loop with concrete state can be
unrolled by `auto` until it reaches the return.

The same execution is the loop's termination evidence. A loop the proof does
not summarize has one route through the verifier, which runs it one bounded
iteration at a time and succeeds only when every feasible path has left it.
The function therefore holds with termination required and declares no
`decreases` clause: there is no invariant bundle for a measure to join, and
nothing left for one to prove.

```c filename=bounded_loop.c
int32 count_to_three() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "bounded_loop.c";

int32 count_to_three() {
    ensures returns_three: result == 3 by auto;
}
```

```expect
pass
```
