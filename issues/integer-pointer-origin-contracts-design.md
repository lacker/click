# Shared contracts for pointer origins carried by integers

Priority: P2.

Soundness: incomplete. Genuine full-width pointer/integer round trips already
retain checked origin, including through storage and supported tagging. Contracts
cannot express that origin for abstract integer inputs or stored words. Click
refuses recovery from numeric equality alone; no false acceptance is known.

## Scope and invariant

Expose the existing distinction between an integer's numeric bits and its
retained complete pointer origin through shared C/C++/Rust contracts. Numeric
equality must never create or transfer origin. Origin includes the source
pointer's position, object/array domain and lifetime designation, not just an
allocation or address. Recovery must retain one-past and expired-object status.
Ownership, initialization and typed-place validity remain separate requirements.

This is deferred from PR #646 by user direction. The bounded profile keeps the
original numeric-only tagged-pointer examples as explicit rejection controls;
their source programs and claims remain unchanged. A future implementation must
add positive verification and audit coverage with explicit origin contracts.

## Intended contract surface

One built-in predicate is proposed, provisionally `pointer_origin(word, p)`:

```click
requires pointer_origin(word, p);
requires (word & ~1u64) == address(p);
```

The first clause describes retained origin; the second proves address restoration.
Use the existing `requires`, `ensures`, resource `fact`, `old` and snapshot forms.
No new statement keyword, ownership clause, tagging operator or nominal integer
type is proposed for the first slice. This syntax is a proposal, not implemented.

The predicate must observe complete values or exact memory reads, not merely
bitvector terms. Ordinary numeric equality/substitution cannot transport it to
an originless value with equal bits. At function entry or resource unfolding it
describes an explicit input promise; modular calls and resource folding must
check the existing origin. Body-checked postconditions transfer origin without
inventing geometry or access rights.

Settle source-position matching, harmless pointer casts, conditional promises
and null handling before implementation. Zero-to-null conversion already has a
separate rule; tagged null values must remain usable without fabricated live
object origin. Do not silently restrict tagged lists to non-null successors.
Start with the existing LP64 full-width signed/unsigned 64-bit integer profile
and its checked preservation/invalidation rules. Language-specific importers
retain responsibility for admitting their casts and compiler guarantees.

## Retained reproductions

The unchanged C and Click fixtures are committed in
[`src/bin/click-audit/tests.rs`](../src/bin/click-audit/tests.rs):

- `numeric_only_witness_contract_refuses_a_masked_pointer_return`: `unpack`
  returns `(struct node *)(node->word & ~1)`. An existential `next` relates
  `node->word` to `address(next)` and a low tag, but promises no origin.
- `numeric_only_recursive_contract_refuses_a_masked_pointer_argument`:
  `count_live` recursively casts the masked word, then branches on its low bit.
  The recursive resource owns the successor and states numerical alignment and
  tag equations, but cannot describe the stored word's origin.

Both normal verification and selected-site expansion must currently reject for
missing integer origin. The same gap affects the existing
[`marked-linked-list`](../examples/marked-linked-list/README.md) resource model.
Existing positive/negative round-trip controls live in
[`src/surface/tests/integer_origin_tests.rs`](../src/surface/tests/integer_origin_tests.rs).

## Acceptance criteria

1. Define a shared, kernel-checked origin relation over complete scalar values
   and immutable reads. Keep numeric reasoning separate and document its exact
   entry, storage, snapshot and modular-call semantics.
2. Verify constructors/tagging helpers that establish the stronger resource
   invariant, its full-width store/load transport, and fold/unfold preservation.
   Calls must reject a missing or mismatched origin premise.
3. Add positive counterparts for both original audit programs and the marked
   linked list, changing contracts only. The unnamed-witness return must expand
   and recheck in fresh state. The recursive audit must preserve the anchored
   wide guard after the call, reverify and reexpand deterministically.
4. Retain rejection of numeric-only equations, forged words, equal-address
   siblings/adjacent rows, truncation, partial overwrites, unsupported operations,
   and dereference of one-past or expired origins. Include nullable successors.
5. Check expansion, retained sessions and modular transfer in the shared kernel;
   cover admitted C/C++/Rust boundaries without inventing cross-language cast
   guarantees. Test indexed origin lookup across multiple unrelated-state sizes.
6. Restore the deferred positive audit coverage, document the supported profile,
   and delete this issue once its implementation and regressions land.
