# A one-past scalar-member pointer can read its sibling

Soundness: unsound. Ordinary C verification accepts dereferencing the pointer
one past a scalar member to read its sibling, despite C11's one-element scalar
array rule. The program's accepted memory-safety/defined-behavior claim is false.
The fixed-baseline recovery audit reproduces this on master `325f9f604` and the
archived implementation `e3d84a785` without changing source or claims.

Priority: P1.

The shared evaluator accepts a C++ and C program that dereferences the pointer
one past a scalar record member to read the following member. Both probes
verified locally during the object-model audit at `8153b3ac0`.

This is a soundness defect, not missing proof automation. Allocation bounds,
matching addresses, initialized typed cells and permission to read the sibling
do not make the original pointer designate that sibling.

## Reproduction

Save the following as a Markdown proof and run `click verify PATH.md` with the
pinned C++ exporter configured. The current result is `1 selected proof verified`.
The required behavior is rejection of the program's undefined dereference.

```cpp filename=pair.cpp function=probe profile=normal_only
struct Pair { int first; int second; };
int probe(Pair& pair) noexcept { return *(&pair.first + 1); }
```

```click
verifying "pair.cpp";
int32 probe(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures result == pair.second;
} by { execute(); simp(); }
```

The C probe also verifies: use a `c filename=pair.c` fence with the same record
and `int probe(struct Pair* pair) { return *(&pair->first + 1); }`, then a
sidecar with `struct Pair* pair` and `pair->first` / `pair->second`.

A second C++ probe also verifies: change the function to return `int*` with
`return &pair.first + 2;`, change the contract result type to `int32*`, and use
`ensures 1 == 1;`. Here pointer formation itself exceeds the scalar member's
one-element domain. No dereference or strong result claim is needed to expose
the missing check.

## Source rule and affected boundary

C++20 N4861 [basic.compound] treats a scalar non-array-element object as an
array of one element for pointer arithmetic. A pointer past its end does not
point to a different object at the same address. [expr.add] permits formation
of the one-past pointer, not dereference of it. C11 6.5.6p7-p8 has the
corresponding one-element-array and one-past restrictions.

`CPointerValue` now has object/array designation terms and domain-aware value
identity, but native producers and checked consumers are not yet enabled.
C++ member-address lowering checks the member's
address, then common pointer arithmetic uses held ranges/allocation bounds.
The subsequent load can find the sibling's typed cell at the resulting address.
`src/kernel/eval/operators.rs`, `src/kernel/eval/memory_loads.rs` and
`src/languages/cpp/lowering.rs` are the relevant paths.

## Acceptance

- Reject the original C and C++ probes, including equivalent forms through a
  pointer local, stored/reloaded pointer, or modular helper. Do not merely match
  the syntax `&field + 1`.
- Reject formation beyond the selected domain's one-past endpoint even when
  the address lies within the enclosing allocation and the contract is trivial.
- Preserve valid scalar-pointer `+ 0`, formation/comparison of one-past pointers
  where the source language permits them, actual array traversal, and direct
  access through `&pair.second`.
- Keep memory aliasing/address equality distinct from typed access validity.
  A pointer comparison or equality rewrite must not upgrade a one-past pointer
  into a dereferenceable sibling pointer.
- Preserve pointer designation through value copying, calls, snapshots and
  supported pointer representation copies. Check the same rules during ordinary,
  expanded and retained verification, with local indexed work.
- Audit C, C++ and Rust lowering against the common rule; do not infer that a
  safe-Rust borrow justifies arbitrary raw-pointer arithmetic.

The [object-model design](../design/cpp-object-model.md#pointer-designation-a-confirmed-shared-gap)
records the required semantic boundary. Byte/word representation work must not
conceal this independent gap.


## Pointer-field address equality countermodel

The former positive regression `c0_const_pointer_fields_alias_proof_expands_and_reverifies`
used this unchanged source and contract:

```c
struct holder { const int *value; };
int update(struct holder *h, int *p) {
    *p = 7;
    return h->value[0];
}
```

```click
verifying "fields.c";
int update(struct holder *h, int *p) {
    views h->value;
    owns p[0..1];
    requires h->value == p;
    ensures result == 7 by auto;
}
```

This positive expectation was invalid. For a live `struct Pair { int first;
int second; } pair`, let `h->value = &pair.first + 1` and `p = &pair.second`.
The pointer-field slot is readable and the second member can be owned. The
addresses compare equal, but the loaded field retains the first member's
one-past designation. Writing through `p` is valid; dereferencing `h->value`
is undefined. The contract supplies no separate validity requirement for that
loaded referent, and equality must not manufacture one.

The original source and contract are now retained as a negative regression,
`c0_const_pointer_field_address_equality_does_not_authenticate_loaded_domain`.
The current verifier refuses the native `return h->value[0];` with
`pointer arithmetic left the pointed-to object`. The separate unchanged
`c0_const_pointer_fields_store_proof_expands_and_reverifies` regression retains
positive coverage for storing and reloading the actual pointer carrier.

## Recovery audit status (2026-10-14)

The [shared object-model recovery audit](../design/object-model-recovery-audit.md)
reran the ordinary C reproduction with `int32` fields, views of both fields and
`ensures result == p->second;` proved by `execute(); simp();`. Both fixed master
`325f9f604` and archive `e3d84a785` accept it. This bug therefore remains open
for ordinary C; native/C++ rejection controls do not establish its closure.
The earlier implementation notes above describe historical checkpoints.
