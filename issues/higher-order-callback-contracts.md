# Give function-pointer parameters checked callback contracts

Found by the 2026-09-04 MVR audit. Click can dispatch a function-pointer call
among compatible concrete functions known to the verified project. Linux's
augmented rbtree core is genuinely generic: exported functions receive an
`augment_rotate` callback, and erase helpers invoke `propagate`, `copy`, and
`rotate` through a caller-supplied `struct rb_augment_callbacks`. Enumerating
all kernel clients is neither modular nor a contract for an arbitrary valid
callback.

## Violated invariant

A call through an abstract function pointer must be checked against an
explicit contract carried by that pointer. Signature compatibility alone
cannot justify its result, memory effects, resource transfers, or preservation
of the rbtree invariant.

## Intended regression

An unchanged rotation helper accepts a callback over two struct pointers,
mutates a small tree fragment, and invokes the callback. Its sidecar requires
the callback to preserve the tree-shape resource while updating only a named
augmentation footprint. Two concrete callbacks satisfying the contract pass;
a callback with an extra write and one that consumes a required resource fail.

A second regression loads three callbacks from a const struct object and
retains the distinct contract associated with each field.

## Acceptance criteria

- Surface Click can declare a contract for a function-pointer parameter and
  for a function pointer loaded from a modeled struct field.
- The contract can quantify over call arguments, name pure pre/postconditions,
  and transfer or borrow ordinary resources and effect footprints.
- Each indirect call checks the callback precondition and applies only its
  declared postcondition and effects; signature matching alone proves nothing.
- Concrete function-pointer formation checks that the target implementation's
  verified contract refines the required callback contract.
- Callback contracts compose through another verified function without
  enumerating all whole-program targets.
- The augmented rbtree callback sites, positive and negative regressions, and
  `scripts/check.sh` pass.

Related: [struct-model.md](struct-model.md),
[global-variables.md](global-variables.md), and
[const-qualified-types.md](const-qualified-types.md).
