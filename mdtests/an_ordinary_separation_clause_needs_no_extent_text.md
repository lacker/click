# An ordinary separation clause needs no extent text

The extent meaning a separation clause now carries costs nothing to state.
This range's endpoints are symbolic and its validity is not decided either
way by the surrounding facts, so the clause is accepted as written: no upper
bound on `n`, no added premise, no repair to the proof.

That is the deliberate limit of the check. A separation is refused only where
the context already proves one of its ranges runs backwards. An undecided
extent is *not* turned into a proof obligation, because a range reached
through a composite clause publishes no extent guard to the code that names
it, so such an obligation would be one no contract text could discharge.
Keeping this case passing is what says the check reads the facts it has
rather than demanding new ones.

```c filename=an_ordinary_separation_clause_needs_no_extent_text.c
int32 ordinary_separation(int32 a[], int32 b[], int32 n) {
    return b[0];
}
```

```click
verifying "an_ordinary_separation_clause_needs_no_extent_text.c";

int32 ordinary_separation(int32 a[], int32 b[], int32 n) {
    requires 0 <= n;
    requires separate(memory(a[0..n]), memory(b[0..1]));
    owns b[0..1];

    ensures result == b[0] by auto;
}
```

```expect
pass
```
