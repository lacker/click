# Preserve object provenance across pointer-parameter boundaries

P1: a helper contract hides undefined pointer ordering in a concrete caller.
Reproduced at `3ad0d2e1`.

## Violated invariant

Pointer ordering and subtraction require their C object relationships to be
proved. Sharing the verifier's external-memory address space does not prove
that two pointers belong to one C array or object. Moving an operation into
a verified helper must not make undefined behavior disappear.

`src/surface/lowering/resource_lowering.rs` represents data-pointer
parameters with `PointerBlock::ExternalArgument` and symbolic offsets.
`apply_same_block_pointer_operation` in `src/kernel/eval/operators.rs`
replaces both offsets with zero before comparing their blocks. Independent
external parameters therefore pass its same-block test unconditionally.
Relational comparisons and pointer subtraction both use this helper.

## Small reproduction

`pointers.c`:

```c
int f(int *p, int *q) {
    return p < q;
}

int g(void) {
    int a = 1;
    int b = 2;
    return f(&a, &b);
}
```

`pointers.click`:

```click
verifying "pointers.c";
int32 f(int32* p, int32* q) {
    views p[0..1];
    views q[0..1];
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 g() {
    ensures result == 0 or result == 1;
} by { execute(); simp(); }
```

`click verify pointers.click` exits 0 for both functions. The caller passes
pointers to unrelated local objects. Their relational comparison has
undefined behavior under [C11 section 6.5.8 paragraph 5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf#page=114).

As a control, a standalone `g` with identical locals and
`return &a < &b;` correctly fails with
`step() produced undefined behavior: pointer arithmetic left the pointed-to object`.
The discrepancy is caused by parameter abstraction and modular verification.
The existing cross-block subtraction fixture covers a local pointer versus
a parameter, which does not exercise the two-external-parameters case.

## Acceptance criteria

- Reject the exact helper/caller reproduction without the required object
  relationship, while preserving the original C source.
- Retain object identity or checked same-object evidence through parameter
  abstraction and contract application. An external address-space tag alone
  must not discharge this obligation.
- Cover all four pointer ordering operators and subtraction with independent
  parameters and concrete callers supplying distinct objects.
- Preserve valid same-array and permitted one-past-end operations, applicable
  aggregate-member ordering, and ordinary pointer equality comparisons.
- Add negative fixture coverage and pass `scripts/check.sh`.
