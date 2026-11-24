# A slot resource a proof `match` selects does not prove a wrong field value

The negative twin of
[`a_proof_match_selects_the_resource_of_a_slot_its_arms_differ_on.md`](a_proof_match_selects_the_resource_of_a_slot_its_arms_differ_on.md):
`kk.v` is 4, not 3.

```c filename=a_proof_match_selected_slot_resource_rej.c
void f(int32* q) { }
```

```click
verifying "a_proof_match_selected_slot_resource_rej.c";

spec enum Sel { A, B }

resource cellA(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource cellB(p: int32*) {
    field w: int32;
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
    fact w == 0;
}

resource root(q: int32*) {
    field sel: Sel;
    field v: int32;
    field u: int32;
    match sel {
        Sel::A => {
            owns k: cellA(q);
            fact k.v == u;
        },
        Sel::B => {
            owns k: cellB(q);
            fact k.v == u;
            fact k.w == v;
        },
    }
}

void f(int32* q) {
    owns r: root(q);
    requires r.sel != Sel::B;
    requires r.v == 3;
    requires r.u == 4;
} by {
    match r.sel {
        Sel::A => {
            let { k: kk } = unfold(r);
            have kk.v == 3 by { close(); }
            step_until(function.exit);
            let r = fold(root(q), { sel: Sel::A, v: 3, u: 4, k: kk });
            close();
        },
        Sel::B => { contradiction(r.sel == Sel::B); },
    }
}
```

```expect
fail: could not establish
```
