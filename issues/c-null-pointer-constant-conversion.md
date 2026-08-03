# Implement C null pointer constant conversion

## Problem

Click understands pointer comparisons with the integer literal `0`, but it does
not consistently understand `0` as a null pointer constant in pointer-valued C
contexts.

The guarded linked-list work exposed this when the natural C implementations
used:

```c
struct node* list_empty() {
    return 0;
}

node->next = 0;
```

The initial return produced a runtime type mismatch. A local experiment that
coerced integer zero to Click's null `Pointer` made symbolic execution produce
the expected pointer, but independent contract certification still replayed
the path as a type mismatch. This is therefore not just parser sugar: execution,
proof construction, and proof replay must agree on the conversion.

The current `examples/linked-list` workaround is to receive an already-typed
pointer and constrain it with `empty == 0`. That keeps the recursive-resource
change focused, but it is not the desired language design. Click should model
the supported C null semantics directly.

## Desired behavior

For every pointer type supported by Click's C0 subset, the integer constant
expression `0` should convert to the canonical null pointer in the ordinary C
conversion contexts Click accepts, including:

- returning `0` from a pointer-returning function;
- assigning `0` to a pointer local or pointer-valued struct field;
- initializing a pointer with `0`;
- passing `0` to a pointer parameter; and
- comparing a pointer with `0` (already supported, and should use the same
  canonical representation).

Nonzero integers must not acquire an implicit integer-to-pointer conversion.
There is no need to add general casts or full C conversion semantics as part of
this issue; implement the null pointer constant for the C0 surface Click
actually supports.

## Kernel and proof-model requirement

Use one canonical null-pointer representation throughout lowering, expression
evaluation, assignment coercion, function-return coercion, specification
lowering, symbolic execution, theorem construction, and independent
certificate replay. It is a correctness bug if the main verifier accepts a
null conversion that kernel certification later reconstructs as
`TypeMismatch`, or vice versa.

While investigating, also separate this from any more general pointer-return
certification gap. Returning an already-typed pointer argument was tried as an
intermediate workaround and also failed independent certification. If pointer
returns are broken independently of null conversion, fix or split that issue
before claiming null returns work.

## Acceptance criteria

- Focused mdtests cover pointer return, local assignment/initialization,
  pointer-field assignment, and pointer-argument passing with `0`.
- The same cases pass both symbolic proof execution and independent contract
  certification.
- Equivalent pointer types in the C0 model, including struct pointers and the
  modeled `int32*`/`uint8*` types, use the same null semantics.
- A focused negative test confirms that a nonzero integer is still rejected in
  a pointer context.
- Pointer comparison with `0` remains compatible with the new conversion path.
- `examples/linked-list` no longer needs an `empty` pointer parameter merely to
  obtain a typed null; its empty constructor can return `0`, and pop may clear
  `node->next` with `0` if that remains the preferred API.
- The full test suite and independent proof-replay gates pass.
