# solve takes a known constructor's payload as the witness

`exists (v: int32) { r == Result<int32, uint8>::Ok(v) }` holds because a fact
fixes `r` to `Ok(5)`: `solve` reads the payload off that constructor and
writes `witness(5)`. A payload a parameter holds is written as the
parameter, `witness(x)`. This is the requirement of a Rust
`Result::unwrap`, so a caller that knows the value meets it by `solve`.

```click
theorem witnesses_a_constant(r: Result<int32, uint8>) {
    requires r == Result<int32, uint8>::Ok(5);
    ensures exists (v: int32) { r == Result<int32, uint8>::Ok(v) } by { close(); }
}

theorem witnesses_a_parameter(o: Option<uint32>, x: uint32) {
    requires o == Option<uint32>::Some(x);
    ensures exists (v: uint32) { Option<uint32>::Some(v) == o } by { close(); }
}
```

```expect
pass
```
