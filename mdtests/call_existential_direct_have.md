# Direct citation of a call-produced existential

```c filename=call_existential_direct_have.c
extern int32 child(int32 x);

int32 parent(int32 x) {
    return child(x);
}
```

```click
verifying "call_existential_direct_have.c";

spec enum Path { Here, There }

function pick(x: int32, path: Path) -> int32 {
    match path {
        Path::Here => x,
        Path::There => x + 1
    }
}

extern int32 child(int32 x) {
    ensures exists (path: Path) { pick(x, path) == result };
}

int32 parent(int32 x) {
    ensures result == result;
} by {
    let r = step(child(x), {});
    have exists (path: Path) { pick(x, path) == r } by {
        assumption();
    }
    step();
    simp();
}
```

```expect
pass
```
