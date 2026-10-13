# A memory read inside an Integer argument keeps a refinement stateful

`bump` sets `*p` to 0, so it does not keep the promise of `KeepsOne` that
`low(to_integer(*p)) == 1` still holds afterwards. Its own postcondition is
about `old(*p)`. The named-contract refinement may use its simpler
state-independent rule only when no clause reads memory, and the read of `*p`
here sits inside an Integer argument to `low`. The state-independence check
used to treat every Integer argument as closed without looking inside, so it
took the simple rule, compared the two postconditions as if no state changed,
and accepted `bump`. Then `apply` verified a postcondition that is false
when its callback is `bump`.

The same contract written with `low` over `int32`, or with `*p == 1`
directly, was already refused.

```c filename=integer_argument_refinement.c
void bump(int32* p) {
    *p = 0;
}

void apply(void (*callback)(int32*), int32* p) {
    callback(p);
}

void caller(int32* p) {
    apply(&bump, p);
}
```

```click
verifying "integer_argument_refinement.c";

function low(z: Integer) -> int32 {
    if z == 1 { 1 } else { 0 }
}

contract void KeepsOne(int32* p) {
    owns *p;
    requires low(to_integer(*p)) == 1;
    ensures low(to_integer(*p)) == 1;
}

void bump(int32* p) {
    owns *p;
    requires low(to_integer(*p)) == 1;
    ensures low(to_integer(old(*p))) == 1 by auto;
}

void apply(void (*callback)(int32*), int32* p) {
    owns *p;
    requires KeepsOne(callback);
    requires low(to_integer(*p)) == 1;
    ensures low(to_integer(*p)) == 1 by auto;
}

void caller(int32* p) {
    owns *p;
    requires low(to_integer(*p)) == 1;
}
```

```expect
fail: function `bump` does not satisfy named contract `KeepsOne`
```
