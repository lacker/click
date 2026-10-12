# Numeric integer equality can recover pointer access without checked origin

Reproduced in the bounded object-model integration on 2026-10-12 by
`numeric_address_equation_cannot_recover_a_sibling_object_designation`.
The verifier accepts this contract and produces a proof certificate:

```c
struct Pair { int first; int second; };
int read_word(unsigned long word, struct Pair* p, int* q) {
    return *((int*)word);
}
```

```click
verifying "word.c";
int32 read_word(uint64 word, struct Pair* p, int32* q) {
    views p->second;
    requires q == &p->second;
    requires word == address(q);
    ensures result == p->second;
} by { execute(); simp(); }
```

The premises establish numeric addresses and permission for `p->second`.
They do not establish that `word` carries a pointer origin designating that
member. In particular, the first member's one-past pointer has that address
without designating a dereferenceable second member. Numeric equality must
not manufacture a full pointer value or erase its subobject bounds.

The integer-to-pointer path currently recovers an address from numeric facts
and gives it the legacy pointer-access behavior. Rejecting designated
pointer-to-integer expressions elsewhere does not prevent this path through
an integer parameter and an address-only pointer parameter.

Acceptance criteria:

- Preserve the source and contract above and reject its unsupported read.
- Numeric equality alone must never transfer checked pointer origin.
- If executable round trips are retained, preserve origin separately through
  supported casts, full-width stores/loads and supported integer operations;
  keep numeric proof rewriting separate from origin transfer.
- Verify genuine supported round trips and reject equal-address sibling,
  one-past, stale-lifetime, and forged-integer cases under the selected profile.
- Recheck ordinary, expanded and retained certificates for the admitted cases.

The decision between implementing checked integer origin now and explicitly
restricting executable round trips is pending; this bug does not choose it.
