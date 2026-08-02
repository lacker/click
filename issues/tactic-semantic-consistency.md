# Remove tactic spelling and semantic traps

## Problem

Several nearly identical Click spellings currently mean different operations:
`by simp;` executes the remaining C and then simplifies, while `by {
simp(); }` only simplifies at the current frontier; `by frame;` performs
contextual reasoning, while `frame()` is an exact simple rule. Separately,
`derive` and `calculate` expose a backend distinction, and two specialized
logical tactics duplicate compositions of ordinary rules.

These are not merely cosmetic names. This issue changes semantics after the
canonical vocabulary and execution model are in place. It depends on
[tactic-execution-unification.md](tactic-execution-unification.md).

## One spelling, one meaning

### `simp`

Make these semantically identical:

```click
by simp;

by {
    simp();
}
```

Both should invoke the simplifier at the current proof state. Neither spelling
should implicitly execute C. A whole function claim that needs execution and
proposition solving should use the omitted default proof or `by auto;`; an
explicit script should write `execute(); simp();`.

### `frame`

Make `by frame;` ordinary sugar for a script containing the same bare smart
`frame()` operation. Adopt the same premise convention as the other paired
tactics:

- `frame()` and `frame(region)` are contextual smart operations.
- `frame() using { fact P; ... }` and the region form are simple operations
  using exactly the listed range and effect premises.
- Empty `using {}` is permitted for a context-free exact frame check.
- Expansion emits only the `using` form.

Do not retain a situation where punctuation alone changes whether range bounds
are derived contextually.

`auto` may remain special: omitted proof clauses and `by auto;` are the default
orchestrator, and there is no need to add an `auto()` script call in this issue.

## Consolidate atomic reasoning

Retain one public exact-premise operation:

```click
derive(P) using {
    fact Q;
    fact R;
}
```

Remove `calculate`. The current distinction between “ordinary kernel theory”
and “simplifier equality/arithmetic theory” is an implementation choice that a
user should not need to encode in source. `derive` should deterministically
select or replay the recorded atomic rule. Internal certificate variants may
remain distinct as long as expansion prints the single public spelling and
replay checks the selected evidence rather than searching for a new proof.

Do not introduce `calc` as an alias. Reserve that familiar name for a future
structured calculation syntax, if Click eventually gains one.

## Remove specialized logical leaves

Remove `double_negation()` and `vacuous()`. They are expressible using the
ordinary logical vocabulary:

- To prove `not (not P)` from `P`, use `intro()` and then
  `contradiction(P)`.
- To prove `A implies B` from `not A`, use `intro()` and then
  `contradiction(A)`.

Update the smart proposition derivation lowerer to emit those compositions.
The kernel rules may remain; they should not require dedicated surface tactic
names.

The vocabulary issue renames `conjunction()` to `split()`. Initially `split()`
may preserve the current deterministic behavior of closing from two exact
facts. If Click later supports interactive subgoal focus, `split` is also the
natural spelling for generating the two conjunction subgoals; no further
rename should be needed.

## Compatibility and diagnostics

- Reject `calculate`, `double_negation`, and `vacuous` with focused messages
  showing the canonical replacement or composition.
- Update failures and help text so `simp` is consistently described as
  simplification, `frame` as frame reasoning, and `auto` as orchestration.
- Do not preserve the old `by simp` execute-then-simplify behavior behind a
  hidden alias. Existing repository proofs must be migrated explicitly so the
  intended sequence is visible.

## Acceptance criteria

- `by simp;`, `by { simp; }`, and `by { simp(); }` invoke the same operation at
  the same proof state, subject only to their existing syntactic wrapper.
- `by frame;` and `by { frame(); }` invoke the same contextual frame operation.
- Bare `frame` is smart; `frame using` is simple, exact-premise, expandable,
  and replayable.
- `derive` covers every current `derive` and `calculate` certificate without
  turning simple replay into proof search.
- `calculate`, `double_negation`, and `vacuous` are absent from accepted source
  and expanded output.
- Smart logical expansion uses `intro`, `split`, `left`, `right`,
  `contradiction`, `derive`, `assumption`, `normalize`, and control-flow `if` as
  needed, with no private source spellings.
- Parser, verifier, expansion, profiler, audit, mdtest, and example coverage is
  updated.
- `docs/proof-tactics.md` becomes the exact canonical inventory, and
  `docs/proof-landscape.md` no longer advertises stale future names such as
  `exact` or `calc` as though they were the current direction.
- The default test suite passes.
