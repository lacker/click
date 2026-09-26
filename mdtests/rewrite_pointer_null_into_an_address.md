# `rewrite` by a null pointer equality reaches an address

A pointer converted to an integer, `(uint64)p`, keeps the pointer inside an
address term. Once a proof has `p == 0`, `rewrite(p == 0)` substitutes null for
`p` there as it does in any pointer position, including in a 64-bit
comparison, and null's address is the integer zero, exactly as evaluating the
C cast yields it. The Linux insert fixup needs this when a context frame's
grandparent is the tree root: the parent word it refolds is stated as
`address(grandparent) + bit`, and at the root `grandparent == 0`.

Before, the pointer rewrite walked only 32-bit conditions and a few operators,
so the equality was reported as not occurring, and `normalize` treated
`address(null)` as an opaque term.

```c filename=null_address.c
struct cell { struct cell *up; };

void keep(struct cell *c) {
}
```

```click
verifying "null_address.c";

spec enum Frame { Above(struct cell*) }

function frame_null(f: Frame) -> int32 {
    match f {
        Frame::Above(up) => if up == 0 { 1 } else { 0 },
    }
}

resource frame_at(c: struct cell*) {
    field model: Frame;
    match model {
        Frame::Above(up) => {
            owns &c->up;
            fact c->up == up;
        },
    }
}

theorem frame_null_is_null(up: struct cell*) {
    requires frame_null(Frame::Above(up)) == 1;

    ensures up == 0 by {
        if up == 0 {
            assumption();
        } else {
            have frame_null(Frame::Above(up)) != 1 by {
                unfold(frame_null(Frame::Above(up)));
                normalize() using { not(up == 0); }
            }
            contradiction(frame_null(Frame::Above(up)) == 1);
        }
    }
}

void keep(struct cell* c) {
    owns f: frame_at(c);
    requires frame_null(f.model) == 1;
} by {
    match f.model {
        Frame::Above(up) => {
            have frame_null(Frame::Above(up)) == 1 by {
                rewrite(Frame::Above(up) == f.model);
                assumption();
            }
            have up == 0 by {
                apply(frame_null_is_null(up)) using {
                    frame_null(Frame::Above(up)) == 1;
                }
                assumption();
            }
            have address(up) + 1 == 1 by {
                rewrite(up == 0);
                normalize();
            }
            execute();
            simp();
        },
    }
}
```

```expect
pass
```
