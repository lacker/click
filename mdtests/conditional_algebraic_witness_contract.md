# A constructed path witness certifies a conditional postcondition

```c filename=conditional_algebraic_witness_contract.c
int32 found(int32 from) { return 1; }
```

```click
verifying "conditional_algebraic_witness_contract.c";
spec enum Path { Here, Left(Path), Right(Path) }
function endpoint(from: int32, path: Path) -> int32 decreases path {
    match path {
        Path::Here => from,
        Path::Left(rest) => endpoint(from, rest),
        Path::Right(rest) => endpoint(from, rest)
    }
}
int32 found(int32 from) {
    ensures result != 0 implies exists (path: Path) { endpoint(from, path) == from };
} by {
    have exists (path: Path) { endpoint(from, path) == from } by {
        witness(path = Path::Left(Path::Here));
        unfold(endpoint(from, Path::Left(Path::Here)));
        unfold(endpoint(from, Path::Here));
        normalize();
    }
    step(); simp();
}
```

```expect
pass
```
