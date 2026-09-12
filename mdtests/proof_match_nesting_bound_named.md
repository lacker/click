# The proof-region nesting bound names itself

The checked proof drivers bound how deeply `match`, `branch`, and proof `if`
regions nest, so a nested descent cannot reserve an unbounded Rust stack. Past
that bound the proof used to be declined as an unsupported shape, with no way
to tell a real limitation from a proof the drivers simply do not accept. It now
says what the bound is and how deep this proof is.

The bound counts regions, not tactics: a linear run of tactics between two
regions continues the region it is in, and the frontier split that picks one
constructor arm out of many is charged separately. Charging both to the
nesting counter made the effective limit five, which is what declined C4's
four-scrutinee `rb_replace_node` proof in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md).
Twelve nested regions is one past the bound; eleven verify.

Repeating the same scrutinee is the cheapest way to write a deep nest. Each
level is a real region: it splits the frontier, closes its `None` arm by
contradiction, and rejoins.

```c filename=proof_match_nesting_bound_named.c
struct cell { int32 value; };

int32 read_one(struct cell *a) {
    return a->value;
}
```

```click
verifying "proof_match_nesting_bound_named.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 read_one(struct cell* a) {
    owns t: cell(a);
    requires t.model != Maybe::None;
    requires a->value == 0;
    ensures result == 0;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Maybe::None => { contradiction(t.model == Maybe::None); },
        Maybe::Some(v0) => {
            match t.model {
                Maybe::None => { contradiction(t.model == Maybe::None); },
                Maybe::Some(v1) => {
                    match t.model {
                        Maybe::None => { contradiction(t.model == Maybe::None); },
                        Maybe::Some(v2) => {
                            match t.model {
                                Maybe::None => { contradiction(t.model == Maybe::None); },
                                Maybe::Some(v3) => {
                                    match t.model {
                                        Maybe::None => { contradiction(t.model == Maybe::None); },
                                        Maybe::Some(v4) => {
                                            match t.model {
                                                Maybe::None => { contradiction(t.model == Maybe::None); },
                                                Maybe::Some(v5) => {
                                                    match t.model {
                                                        Maybe::None => { contradiction(t.model == Maybe::None); },
                                                        Maybe::Some(v6) => {
                                                            match t.model {
                                                                Maybe::None => { contradiction(t.model == Maybe::None); },
                                                                Maybe::Some(v7) => {
                                                                    match t.model {
                                                                        Maybe::None => { contradiction(t.model == Maybe::None); },
                                                                        Maybe::Some(v8) => {
                                                                            match t.model {
                                                                                Maybe::None => { contradiction(t.model == Maybe::None); },
                                                                                Maybe::Some(v9) => {
                                                                                    match t.model {
                                                                                        Maybe::None => { contradiction(t.model == Maybe::None); },
                                                                                        Maybe::Some(v10) => {
                                                                                            match t.model {
                                                                                                Maybe::None => { contradiction(t.model == Maybe::None); },
                                                                                                Maybe::Some(v11) => {
                                                                                                    unfold(t);
                                                                                                    execute();
                                                                                                    let t = fold(cell(a), { model: old(t.model) }, {});
                                                                                                    simp();
                                                                                                },
                                                                                            }
                                                                                        },
                                                                                    }
                                                                                },
                                                                            }
                                                                        },
                                                                    }
                                                                },
                                                            }
                                                        },
                                                    }
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}
```

```expect
fail: this proof nests 12 execution regions; the checked proof drivers support at most 11
```
