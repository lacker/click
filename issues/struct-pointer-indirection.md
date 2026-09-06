# Support pointer-to-pointer forms for struct pointers

Found by the 2026-09-04 MVR audit. C0 retains a struct name for `struct S *`
but explicitly rejects pointer depth beyond that form. Linux rbtree insertion
helpers use `struct rb_node **link`, initialize it with the address of a root
or child field, redirect it while descending, and finally store a node through
it.

## Violated invariant

Taking the address of a struct-pointer cell must produce a typed pointer to
that cell, preserving the cell's allocation provenance and the pointee struct
identity. A store through `struct S **` must update exactly that pointer cell,
not retag it as an integer-pointer array.

## Intended regression

An unchanged C fixture walks a binary tree with `struct node **link`, assigning
`link = &parent->left` or `&parent->right`, and writes `*link = node`. The proof
shows that only the selected pointer field changes. Negative coverage rejects
incompatible struct names, a pointer-to-pointer with the wrong field type, and
unsupported deeper indirection.

## Acceptance criteria

- C0 retains the complete `struct S **` surface type, including its struct-tag
  metadata and qualifiers. The kernel keeps the existing eight-byte
  pointer-cell ABI and pointer provenance; nominal struct identity is checked
  before lowering because kernel `CType` intentionally has no aggregate-tag
  variant.
- Address-taking of local, global, direct-field, and nested-field
  `struct S *` lvalues produces the same typed cell pointer.
- Loads and stores through `struct S **` preserve the stored pointer's
  provenance and update precisely one pointer-width cell.
- Function parameters, returns where supported, function-pointer signatures,
  and resource footprints can name the type; higher-order function contracts
  remain separately tracked.
- Incompatible struct identities are rejected rather than collapsed to the
  existing generic `int32 **` representation at the C0 boundary. The generic
  kernel cell representation is safe only after that check has succeeded.
- The rbtree link-walk regression and `scripts/check.sh` pass.

The implementation slices cover local, parameter, and file-scope `struct S **`
objects, direct and nested field addresses, `*link` pointer-cell stores, and
nominal identity across pointer-valued function returns. Function-pointer
parameters and locals now retain nominal struct-pointer tags in callback
metadata, check known callback targets and indirect arguments before lowering,
and keep the kernel's generic pointer representation. Named contracts for
abstract function-pointer values are tracked separately in
`issues/function-contracts.md`. Click contract signatures spell the type as
`struct S** name` (2026-09-05, `mdtests/rb_parent_family.md` passes a link slot
to `rb_link_node`).

Related: [struct-model.md](struct-model.md).
