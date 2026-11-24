# Apply a resource tactic to a returned value

The application shapes the resources the proof holds at function exit.
One caller proves the requirement explicitly, and the others use the
ordinary obligation solver. The branch proof applies the tactic separately
to each return.

```c filename=user_tactic_at_return.c
struct pr { int32 a; int32 b; };

int32 explicit_proof(struct pr *p, int32 n) { return n; }
int32 implicit_proof(struct pr *p, int32 n) { return n; }
void void_proof(struct pr *p) {}
void by_child_path(struct pr *p) {}
int32 returned_from_branch(struct pr *p, int32 flag) {
    if (flag != 0) {
        return 7;
    } else {
        return 9;
    }
}
```

```click
verifying "user_tactic_at_return.c";

resource both(p: struct pr*) {
    field tag: int32;
    owns p->a;
    owns p->b;
}

resource first(p: struct pr*) {
    field tag: int32;
    owns p->a;
}

resource second(p: struct pr*) {
    field tag: int32;
    owns p->b;
}

resource wrapper(p: struct pr*) {
    owns child: first(p);
}

tactic divide(p: struct pr*, n: int32) {
    consumes x: both(p);
    requires n > 0;
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == n;
} by {
    unfold(x);
    let y = fold(first(p), { tag: n });
    let z = fold(second(p), { tag: 0 });
    have y.tag == n;
}

tactic check_tag(p: struct pr*, n: int32) {
    owns item: first(p);
    requires item.tag == n;
    ensures item.tag == n;
} by {
    have item.tag == n by close();
}

int32 explicit_proof(struct pr* p, int32 n) {
    requires n > 0;
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == result;
} by {
    step_until(function.exit);
    let { y: y, z: z } = divide(p, result, { x: x }) by {
        have result == old(n) by close();
        close();
    }
    check_tag(p, result, { item: y });
    unfold(y);
    fold(y);
}

int32 implicit_proof(struct pr* p, int32 n) {
    requires n >= 2;
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == result;
} by {
    step_until(function.exit);
    let { y: y, z: z } = divide(p, result, { x: x });
}

void void_proof(struct pr* p) {
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == 4;
} by {
    step_until(function.exit);
    let { y: y, z: z } = divide(p, 4, { x: x });
}

void by_child_path(struct pr* p) {
    owns r: wrapper(p);
    requires r.child.tag == 5;
} by {
    step_until(function.exit);
    unfold(r);
    check_tag(p, 5, { item: r.child });
    fold(r);
}

int32 returned_from_branch(struct pr* p, int32 flag) {
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == result;
} by {
    branch {
        true => {
            step_until(function.exit);
            let { y: y, z: z } = divide(p, result, { x: x });
        }
        false => {
            step_until(function.exit);
            let { y: y, z: z } = divide(p, result, { x: x });
        }
    }
}
```

```expect
pass
```
