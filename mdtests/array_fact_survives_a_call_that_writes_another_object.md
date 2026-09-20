# a fact about an array survives a call that may write only another object

`touch_g` declares that it may write `g[0..1]`, and two file-scope declarations
are two objects, so nothing the call may write is in `h`. The checked write set
is the one thing the recorded edge says about the code behind the call, and a
fact about `h` as a whole is carried across it on that alone — no stated
`separate(...)` is read, and none is needed.

```c filename=array_fact_survives_a_call_that_writes_another_object.c
int32 g[4];
int32 h[4];

void touch_g() {
    g[0] = 1;
}

int32 keep_h() {
    touch_g();
    return h[0];
}
```

```click
verifying "array_fact_survives_a_call_that_writes_another_object.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void touch_g() {
    owns g[0..1];
} by {
    execute();
    simp();
}

int32 keep_h() {
    requires h[0] == 5;
    owns g[0..1];
    views h[0..1];
    ensures result == 5;
} by {
    have 0 <= 0 by { simp(); }
    have icount(h, 0, 0) == 0 by {
        unfold(icount(h, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    execute();
    have icount(h, 0, 0) == 0 by { simp(); }
    simp();
}
```

```expect
pass
```
