# C++ raw pointer inputs fall through the legacy domain evaluator

An admitted native C++ raw pointer formal without a typed resource promise
receives no pointer designation. Native arithmetic then uses the legacy
address evaluator and can certify a body whose pointer arithmetic is not
defined for every permitted input. An unknown native input must retain an
unresolved identity; its signature supplies no object, permissions, or extent.

Reproduced offline on 2026-10-11 with the bounded model's CLI10 checkpoint:
`click verify --trace-proof raw_offset /tmp/cpp-bounded-raw-input.md` exits 0.
The trace steps through `declare q` and `return 0` and certifies the contract.
The function may receive a null pointer, for which `p + 1` is undefined.

```cpp filename=raw.cpp function=raw_offset profile=scalar_int32
int raw_offset(int* p) {
    int* q = p + 1;
    return 0;
}
```

```click
verifying "raw.cpp";
int32 raw_offset(int32* p) {
    ensures result == 0;
} by { execute(); simp(); }
```

Acceptance criteria:

- Reject the original body without a native object/range promise and accept
  it with its existing source unchanged and a checked typed prefix contract.
- Allow forwarding an unresolved pointer without dereferencing or offsetting
  it, retaining the complete carrier or an opaque unresolved summary result.
- Enroll pointers only from authenticated native C++ declaration metadata;
  preserve existing C/Rust legacy profiles and qualifiers.
- Preserve the profile through interface reconstruction and retained proof
  identity; a legacy actual argument or address equality must not grant it
  an authenticated object through a result summary.
