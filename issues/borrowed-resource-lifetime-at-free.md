# Define borrowed-resource lifetime at `free`

## Problem

The first vector-growth design gave `vector_copy` a viewed
`allocated_int32s(source, length)` resource, then freed the source allocation.
After the call, the view remained in the caller's ghost context. `free`
consumed ownership, but the stale view survived until final certification and
caused a ghost-resource mismatch.

The verifier should reject or discharge this conflict at the operation that
creates it. It should not allow a view of a lifetime to silently outlive that
lifetime and fail much later.

## Design question

Click needs one explicit rule for views across deallocation:

- If `views` are persistent logical observations, `free` must require proof that
  no view may refer to the allocation and fail locally when one remains.
- If call-site views are scoped borrows, opaque-call application must retire the
  borrow when the call returns while preserving the caller's underlying owned
  resource.

Do not implement both interpretations opportunistically. Choose and document
one rule, including nested composite views and views derived from ownership.
The rule must prevent reading freed memory and remain kernel-checkable.

## Regression

Create focused positive and negative mdtests:

- borrow an owned allocation for a read-only helper and then legally free it;
- retain an explicitly persistent view and reject `free` at that statement;
- repeat both through a composite resource containing allocation authority and
  memory;
- ensure a separated view of another allocation survives.

## Acceptance criteria

- The lifetime of a `views` clause is documented and unambiguous.
- Legal borrow-copy-free composition verifies without leaked ghost views.
- Illegal stale views fail at `free`, not final contract certification.
- Composite and direct resources follow the same kernel rule.
