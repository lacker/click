# Recovery loses a declared record pointer through a modular identity call

Soundness: incomplete. The recovery object model rejects a caller that passes a
live declared record through an identity helper, then reads its first member.
No false acceptance is demonstrated by this reproduction.

Priority: P2. Blocks activation of the recovery model.

## Reproduction

On recovery checkpoint `2cab205db`, run with the gate stack setting:

```sh
RUST_MIN_STACK=8388608 cargo test --lib \
  canonical_surface_record_pointer_identity_transports_declared_domain_modularly
```

The same failure reproduces with the canonical opaque C value-input prerequisite
in checkpoint `d06045be7`. The original regression's C is unchanged:

```c
struct Pair { int first; int second; };
struct Pair *identity(struct Pair *pair) { return pair; }
int caller(void) {
    struct Pair pair = { 7, 9 };
    struct Pair *q = identity(&pair);
    return q->first;
}
```

```click
verifying "identity.c";
struct Pair* identity(struct Pair* pair) {
    views pair->first;
    ensures result == pair;
} by { execute(); simp(); }
int32 caller() {
    ensures result == 7;
} by { execute(); simp(); }
```

Recovery rejects `caller.contract` at tactic 0 with invalid memory access at
`return q->first;`, operation `&q->first`. This is a recovery-specific result;
these runs do not establish a failure on current upstream.

## Acceptance

Retain the original C, resource requirement and claims. Preserve the complete
actual argument's pointer identity through the independently checked return,
so the caller can read the declared record. Do not treat `result == pair` alone
as full-pointer identity: an address equation must not authenticate a one-past,
forged, or unrelated loaded pointer. Pass fresh, expanded, rewritten and retained
checking, and keep the pointer-field address-equality rejection control negative.
