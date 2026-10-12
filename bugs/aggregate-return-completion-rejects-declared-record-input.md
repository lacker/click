# Aggregate return completion rejects the declared record-input proof

Reproduced in the bounded object-model integration on 2026-10-12 by
`surface::tests::contract_tests::aggregate_return_claims_retain_checked_completions`
(focused run 49b, exit 100). The original fixture is
`mdtests/struct_aggregate_return_postcondition.md`.

The source returns a complete record through its declared pointer:

```c
struct inner { int32 value; uint8 flag; };
struct packet { uint8 tag; struct inner inner; int32 tail; };
struct packet clone_packet(struct packet* source) { return *source; }
```

The unchanged contract views all four scalar fields and proves that each
result field equals its corresponding source field, using `auto`. Verification
now rejects the checked completion:

```text
clone_packet.contract claim Ensure(0) on path 0 has mismatched proposition
completion evidence: the checked path outcome is a function-contract runtime
error: clone_packet returned an invalid struct value
```

The complete-carrier copy check must authenticate this declared record input
consistently in source execution and retained completion. It must not recover
a complete object from an equal-address scalar/row pointer. The exact failing
carrier reconstruction remains to be diagnosed; the error alone does not
justify relaxing the check.

Acceptance criteria:

- Preserve the original source and all four field-equality claims.
- Pass the existing ordinary, expanded and retained-completion regression.
- Retain rejection of row, one-past, forged-layout and unauthenticated native
  carriers at aggregate assignment, by-value argument and return boundaries.
- Do not grant ownership or initialize padding through object authentication.
