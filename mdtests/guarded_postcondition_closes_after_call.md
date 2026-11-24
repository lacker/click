# An unconditional arithmetic postcondition is available after a call

The callee proves both the stated equality and the sum's domain. The caller
can use the equality directly, including in a selected-premise proof.
The explicitly guarded counterpart is covered in
[`explicit_guarded_postcondition_closes_after_call.md`](explicit_guarded_postcondition_closes_after_call.md).

```c filename=guarded_postcondition_closes_after_call.c
struct box {
    int v;
};

int pick(struct box* b) {
    return 0;
}

int caller(struct box* b) {
    int got;
    got = pick(b);
    if (got == 0) {
        return 0;
    }
    return 1;
}

int restricted(struct box* b) {
    int got;
    got = pick(b);
    if (got == 0) {
        return 0;
    }
    return 1;
}
```

```click
resource counted(b: struct box*) {
    field live: int32;
    owns *b;
    fact 0 <= live;
    fact live <= 100;
}

verifying "guarded_postcondition_closes_after_call.c";

int32 pick(struct box* b) {
    owns st: counted(b);
    ensures result == 0 or result == 1;
    ensures to_integer(st.live) == to_integer(old(st.live) + result);
} by {
    let { live: n } = unfold(st);
    let st = fold(counted(b), { live: n });
}

int32 caller(struct box* b) {
    owns st: counted(b);
    requires st.live == 1;
    ensures result == 0 implies st.live == 1;
} by {
    step();
    step(pick, { st: st });
}

int32 restricted(struct box* b) {
    owns st: counted(b);
    requires st.live == 1;
    ensures result == 0 implies st.live == 1;
} by {
    step();
    mark m;
    step(pick, { st: st });
    step();
    branch {
        true => {
            have got == 0 by {
                close();
            }
            have at(m, st.live) == 1 by {
                close();
            }
            have st.live == 1 by {
                close() using {
                    to_integer(st.live) == to_integer(at(m, st.live) + got);
                    got == 0;
                    at(m, st.live) == 1;
                };
            }
            step();
            close();
        }
        false => {}
    }
    step();
    close();
}
```

```expect
pass
```
