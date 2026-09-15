# P2: Lower a dependent composite argument in every tactic position

## Violated invariant

A contract's resource clauses are read as one set: a clause whose argument
loads a cell another clause holds, `owns pair(node)` supplying the link that
`owns pair(node->left->left)` loads, is addressable wherever the clause set
is. This holds at a function's own entry, at a named contract's preparation,
and, since 2026-09-15, at every call form (`mdtests/contract_owns_composite_argument_call.md`,
`mdtests/contract_owns_composite_argument_across_forms.md`). It does not yet
hold for a proof tactic that names such a resource: the tactic lowers its
argument against the proof state alone, and in two positions that state
does not supply the link the clause set would.

Neither position is needed by any proof in the corpus today, and the plain
C shapes behind them verify with `execute(); simp();` and no tactic about the
composite at all. This is a proof-script gap, not a language or soundness
gap; both failures are prompt refusals.

## Reproductions (verified 2026-09-15)

1. **`unfold` after `execute()` at the outcome.** With
   `resource leaf_cell(l: struct leaf*) { owns l->value; }` and
   `resource tree(r: struct root*) { owns r->leaf; owns leaf_cell(r->leaf); }`,
   a function that owns `tree(r)` and whose proof is
   `execute(); unfold(tree(r)); unfold(leaf_cell(r->leaf)); ...` fails at the
   second unfold with
   `missing pure fact: loadable(base=r, bytes=8)`. The same two unfolds
   written before `execute()` lower (`mdtests/c_chained_field_access.md`,
   `deep_get`). The outcome state holds `r->leaf` through the first unfold,
   so the second argument should lower there as it does at entry.
2. **`observe` of a dependent argument inside an execution theorem's
   block.** With `pair(node) { owns node[0..1]; owns node->left[0..1]; }`
   and the contract of `mdtests/contract_owns_composite_argument.md`, a
   `theorem ... executes probe(struct node* node) { ensures DependentPair(&probe)
   by { observe(pair(node)); observe(pair(node->left->left)); execute(); simp(); } }`
   fails at the second observe with
   `could not lower resource `pair` argument 0: the kernel evaluation
   produced 0 paths, not one`. The same two observes lower in an ordinary
   function body with the same clauses. The theorem block's entry state is
   the target contract's clause set, so the argument should lower there as
   it does in the function.

Both come from one place: tactic argument lowering (`observe`, `unfold`,
`fold`, `open`) evaluates a declared resource's arguments in the current
proof state without the whole-clause-set supply that
`evaluate_function_resource_context_with_metadata` gives the entry and that
the call boundary now gives its preconditions and returned borrows
(`precondition_state` and `opened_composite_read_views` in
`src/kernel/functions.rs`). The tactic path is in
`src/surface/lowering/resource_lowering.rs` (`lower_resource_clause_at_state`
and the argument evaluation it calls) and `src/surface/proof/resources.rs`.

A third, smaller item found while reducing these: an element range on a
struct pointer counts int32 cells, so `node[0..1]` on a `struct node*` is
four bytes, not one struct element. Two mis-spelled probes were refused
correctly (overlapping owned ranges; a missing view for the field at offset
eight), but nothing in `docs/concepts/resources.md` says which unit the
range counts.

## Small intended regressions

- `mdtests/unfold_dependent_composite_after_execute.md`: reproduction 1 with
  the two unfolds after `execute()`, expecting `pass`, plus its negative
  where the first unfold is omitted, expecting the loadable refusal.
- `mdtests/theorem_observes_dependent_composite_argument.md`: reproduction 2
  expecting `pass`, plus its negative where `observe(pair(node))` is omitted,
  expecting the same refusal the function body gives.
- One sentence in the element-width section of `docs/concepts/resources.md`
  stating the unit of an element range on a struct pointer, with the
  existing `verified-example` mechanism if an example is added.

## Acceptance criteria

- A tactic that names a declared resource lowers its arguments against the
  proof state supplied the way an entry is: the cells the state's own owned
  composites hold, opened one level through their definitions, are
  readable for the argument's loads. Read authority only; nothing is
  owned twice, and a load the state cannot justify is still refused with
  the existing `missing pure fact: loadable(...)` wording.
- The two positive fixtures pass and the two negatives keep their refusals.
- No change to what `execute()` alone proves for the plain C shapes; the
  fixtures above and `mdtests/contract_owns_composite_argument_*.md` stay
  green.
- The element-range unit is documented.
- `scripts/check.sh` passes.
