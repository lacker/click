# Conditional call-result existential has an exact historical spelling

The call guarantee uses its evaluated C argument. The historical logical read
names that same value without adding a validity guard inside the existential.
The proof cites and opens the guarantee directly; read validity is a separate
claim. The child result prevents a tautological witness from closing the goal.

```c filename=conditional_call_existential_historical_read.c
extern int32 child(int32 *a, int32 *b, int32 n, int32 x);

int32 parent(int32 *a, int32 *b, int32 n, int32 i) {
    if (child(a, b, n, a[i])) return 1;
    return 0;
}
```

```click
verifying "conditional_call_existential_historical_read.c";

spec enum Path { Here, There }

function pick(x: int32, path: Path) -> int32 {
    match path {
        Path::Here => x,
        Path::There => x + 1
    }
}

extern int32 child(int32 *a, int32 *b, int32 n, int32 x) {
    views a[0..n];
    owns b[0..1];
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures result != 0 implies exists (path: Path) { pick(x, path) == result };
}

int32 parent(int32 *a, int32 *b, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    views a[0..n];
    owns b[0..1];
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures result == result;
} by {
    mark before_call;
    let r = step(child(a, b, n, a[i]), {});
    branch {
        then {
            have r != 0 implies exists (path: Path) {
                pick(at(before_call, a[i]), path) == r
            } by { assumption(); }
            have exists (path: Path) {
                pick(at(before_call, a[i]), path) == r
            } by { simp(); }
            let (rest: Path) satisfy {
                pick(at(before_call, a[i]), rest) == r
            };
            execute();
            simp();
        }
        else {}
    }
    step();
    simp();
}
```

```expect
pass
```
