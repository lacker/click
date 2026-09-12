# Add abstract summaries for recursive memory structures

P1: required for MVR. A directly recursive composite resource can own an
arbitrary finite binary tree, but ownership alone does not state the tree's
abstract contents or in-order sequence. Linear ownership prevents resource
duplication or loss, but a contract that merely consumes one well-formed tree
and produces another cannot state the API theorem that the exact node
sequence is unchanged. Linux rbtree does not store keys itself, so its generic
correctness property is preservation of node identity and in-order order
while links and colors change.

The core ADT and list foundation is implemented. Recursive `HeapTree` fields
connect parent models to child models across ownership and mutation; the
derived in-order list has a checked left-rotation preservation theorem; the
unchanged initializer and left rotation in
[`examples/modeled-binary-tree`](../examples/modeled-binary-tree/README.md)
verify against an exact model carrying node addresses, payloads, and both
subtrees. Parent-word tagging with the unchanged Linux helper shapes is
prototyped in `mdtests/rb_parent_family.md`.

This document was rewritten on 2026-09-11 as the plan for the remaining
work. It records the design decisions taken, the verified gaps with their
reproductions, and the work packages in dependency order for delegation.
General ADT completeness stays P2 under
[algebraic-data-types.md](algebraic-data-types.md); loop termination stays in
[structural-loop-termination.md](structural-loop-termination.md) but its
surface spelling is decided here (D6). Synthetic examples are development
regressions; the target is the pinned unchanged Linux implementation, whose
import is owned by [kernel-scale-preprocessing.md](kernel-scale-preprocessing.md).

## Violated invariant

Contracts for a mutable recursive structure must be able to relate its finite
abstract model before and after mutation. The model must be derived from the
owned structure, not supplied as an unconstrained ghost assertion.

## Intended regression

Define an abstract model for a binary tree whose in-order sequence contains
node identities. Verify unchanged left- and right-rotation functions with
contracts showing that:

- the output contains exactly the input nodes;
- the in-order sequence is unchanged;
- parent/child links are consistent; and
- no node is duplicated or omitted.

Negative rotations that drop a subtree, reuse one child twice, or swap the
in-order position of two nodes must fail even if the output can still be
folded as some binary tree.

## Verified gaps (2026-09-11)

Each was reproduced against the current binary. The reproductions are small
enough to become the first regression of the package that fixes them.

1. **A loop cannot hold a modeled instance.** A loop header with
   `owns c: cell(node);` fails to parse at the colon; the unnamed
   `owns cell(node);` is refused with "resource `cell` has fields; bind it
   with `owns name: cell(...);`". Every rbtree loop must carry a context and
   a current subtree with model invariants, so nothing beyond rotation can be
   proved today. Package A3.
2. **A model-gated composite exposes no cells at contract lowering or loop
   heads.** With `resource cell(p) { field model: Maybe; match model { None
   => { fact p == 0; }, Some(v) => { owns p->value; fact p->value == v; } } }`,
   the contract `owns c: cell(node); requires c.model != Maybe::None;
   requires node->value >= 0;` fails with `missing pure fact:
   loadable(base=node, bytes=4)`. The positive spelling
   `requires exists (v: int32) { c.model == Maybe::Some(v) };` fails
   identically. The `if`-guarded memory-only body has no such gate. The
   original finding from the function-contracts close-out is the same defect:
   `mdtests/augment_rotate_model_callback.md` contracts its helper over the
   root's raw link cells instead of one folded `tree_at(node)`. Package A1.
3. **A matched arm may only own children of its own resource.**
   `src/surface/validation/algebraic_types.rs` rejects any other family with
   "this slice supports direct recursive children of the same resource". A
   context frame must own a sibling `tree_at`, so the zipper in D3 cannot be
   declared. Package A2.
4. **Loop `decreases` accepts only integer expressions.** The structural form
   exists only on recursive C functions and is spelled
   `decreases resource list(node)`. Package A4, spelling per D6.
5. **A struct-pointer constructor binding cannot be a memory base inside an
   arm body.** Found by package A2: with `Context::Left(parent, ...) => {
   owns parent->value; ... }`, fold fails with `could not evaluate instance
   memory body` and width-unknown loads. `parse_algebraic_field_type` keeps
   only the C type of a spec-enum field and drops the struct name, and arm
   bindings are registered as contract bindings but not as struct
   parameters, so `resolve_field_metadata` finds no layout for `parent`. The
   D3 spelling `ctx_at(child)` keys the frame by the focused child and owns
   the parent's cells through the binding, so this blocks B1 and C1. A2's
   fixture keys the frame by its own node instead. Package A5.
6. **A pointer-typed model payload cannot be related to a C pointer.** Found
   by package B2 on `tree_contains`: the C test is `root == target`, the model
   test is `node == target` with `node` the `HeapTree::Node` identity binding,
   and the resource fact `p == identity` cannot bridge them. `have node ==
   target by { simp(); }` and a pure accessor `heap_node(t.model) == root`
   both fail with `the kernel lowering produced 0 paths, not one`;
   `normalize() using { node == target; }` reports the premise is not exactly
   available. Compounding it, match-arm bindings are out of scope inside a
   nested `branch` or proof `if` arm, a `have` mentioning a C variable loses
   the arm bindings, and a `have` mentioning a binding cannot mention a C
   variable. Traversal results and membership are MVR claims, so this blocks
   B2's membership postcondition, C4, and every "designated node" claim.
   Package A6.
7. **Structural termination ignores matched bodies.** Found by package B2:
   `structural_resource_children` in `src/kernel/termination.rs` requires an
   `if`-guarded body and walks `contains()`, so `decreases resource
   tree_at(root)` is refused ("has fields; bind it with `owns name: ...`")
   and no spelling names a fielded child. Package A4 must accept a matched
   body's named arm children, for functions and loops alike.
8. **A pure function cannot return a bare pointer type.** Found by package
   A6: `evaluate_spec_pure_function_application_paths` builds results with
   `c_value_from_bitvector_term`, which has no opaque pointer term, so an
   accessor `heap_node(t) -> struct tree_node*` cannot be lowered. Adding one
   means a new pointer-block variant with congruence, substitution,
   canonicalization, and block-distinctness rules, which is a
   soundness-sensitive kernel package. Not scheduled: state traversal results
   through `inorder` and list constructors instead (`exists (rest) {
   rb_inorder(m) == List::Cons(result, rest) }`), and revisit only if a
   required contract cannot be spelled that way.
9. **A C call result used directly in a condition has no surface name.**
   Found by package A6 on the scaffold's `tree_contains`: `if
   (tree_contains(root->left, target)) return 1;` leaves the branch fact
   `v1000001 != 0` and the contract fact `v1000001 == heap_member(...)` with
   no way to state the equation between them, so the unguarded `ensures
   result == heap_member(old(t.model), target)` does not verify; the guarded
   `root == target implies ...` form does. Package A7.
10. **An `if` expression cannot produce an algebraic value.** Found by
    package C2: `if flag == 0 { xs } else { List::Nil }` in a pure function
    is refused with "algebraic values are only valid in algebraic equality
    or as a `match` scrutinee", so `list_remove_first` is not definable. C2
    states erasure as append equations instead (`A ++ [erased] ++ B` at
    entry, `A ++ B` at exit), which is stronger. Not scheduled unless a
    required contract needs the conditional form. Also from C2: `predicate`
    has no `decreases` clause, so recursive invariants are `int32`-valued
    pure functions; and a `witness` needs a term no pure function can
    produce for pointers, so the in-order successor is named by hypothesis
    (`rb_min_list(right) == Cons(successor, Nil)`) that a C proof supplies.
11. **`click audit` disagrees with `click verify` on the scaffold.** Found by
    package A7 and reproduced on the sidecar before A7's change: `click audit
    examples/modeled-binary-tree` fails at the first `branch`'s `simp` in
    `tree_contains` with "Grouped proof has no source tactic 9" while
    `verify` passes. Audit is not in `scripts/check.sh`. This is a tooling
    failure under `AGENTS.md` and is package T1, dispatched ahead of further
    proof work. Smaller A7 findings, not scheduled: a match-arm binding
    cannot be a theorem argument inside `have` (`apply_theorem_using` skips
    the fixed-state local substitution; work around with the instance field
    plus a bridge equality); `apply`/`extract` at the top level of a `branch`
    arm is refused by the grouped driver (wrap them in a `have`); and a
    `simp() using` premise naming a bound call result fails to lower when
    the goal names it too (use `rewrite` plus `normalize`).
12. **Proof `match` is capped at two constructors.** Found by package C1:
    `match c.model` over the three-constructor `Context` is refused with
    "proof match currently supports one or two constructors; wider execution
    joins are not implemented" (`src/surface/proof/proof_object/match_cases.rs`).
    Removing the guard let a three-arm match plan and run through the
    existing binary range split, so the guard looks stale, but it needs its
    own regression and review. Package A8. Also from C1, not scheduled: a
    `have` placed after `execute()` does not reach the post-return fold
    recheck, so facts a return-path fold needs go before `execute()`; a
    match-arm binding as a bare argument in a purely pure `have` goal is
    "not an algebraic binding in this scope" while the same binding beside a
    C operand works; and `exists` cannot quantify an ADT-typed variable. A
    failed pure `simp` printed a full Rust debug dump of the proposition and
    schemas twice, which is the raw-state-dump class of diagnostic defect;
    package T2.
13. **A loop body cannot unfold its binder.** Found by package A4: at an
    arbitrary loop head the binder's model is a fresh symbolic value, arm
    selection from the invariants yields only the variant, and `unfold`
    requires constructor evidence ("resource match requires constructor
    evidence for the instance field"). The two ways to get a constructor
    are closed: proof `match` on a model is refused at a loop-body frontier
    ("proof `match` currently requires unchanged function entry"), and a
    pure `int32 -> enum` function cannot be written because an `if` body
    cannot produce an algebraic value (gap 10). So A4 landed the parser,
    the matched-body structural children, the loop back-edge rule, the
    head-time binder arguments, and arm views at loop heads, but no
    positive descending, ascending, or rotate-then-ascend loop fixture.
    Every rbtree loop needs this. Package A9.
14. **`click audit` fails on other examples.** Found by package T1: a
    partial `click audit --keep-going examples` run failed at
    `examples/arena/arena.click:59:9`, `110:13`, `127:13`, `133:13`,
    `160:13` and `examples/bounded-pool/bounded_pool.click:214:5` with a
    different mode from gap 11, for example `could not lower 'have'
    proposition: the kernel lowering produced 0 paths`; confirmed
    pre-existing on an unmodified base. Package T3.
15. **Wide proof matches are superlinear.** Found by package A8: a debug
    `click verify` on an N-arm execution match with identical arms takes
    0.08 s at 4 arms, 0.49 s at 16, and 6.6 s at 32, about thirteen times
    per doubling; `click profile` puts most of it in the frontier split and
    join bookkeeping (deep clones of proof and contract expressions), not
    in tactics or certification, and nested `branch` joins scale the same
    way. The rbtree's three-arm matches are unaffected. This violates the
    complexity contract in `docs/internals/verification-efficiency.md`.
    Package T4.
16. **A fold inside a proof-match arm loses facts about owned, unwritten
    cells after a sibling write.** Found by package A8, pre-existing: in a
    two-constructor match whose arm owns `parent->__rb_parent_color` and
    `parent->rb_left` and states `fact parent->__rb_parent_color == 1`,
    executing a write to `parent->rb_left` and then folding fails with
    `fold requires the instance body facts for the proposed fields`; the
    identical proof with `requires c.model == Context::Left(...)` instead
    of the match arm passes. Every rbtree fixup step writes one link and
    refolds a frame whose other facts are unchanged, so this blocks C3 and
    C5. Package A10.
17. **Remaining audit disagreements after T3.** T3 took the full examples
    audit from 12 site failures to 3 (400 of 457 sites pass; the
    multifile-registry session failure is the quarantined pre-existing
    verify failure). Left: (a) `marked_linked_list.click:80:5`: the
    expansion prints a `let ... where` witness as `symbolic-pointer:...@0`
    because a witness has no surface spelling, and the only diagnostic is
    the parse error; a language decision, deferred with the other language
    questions, but expansion must refuse with the real reason; (b)
    `marked_linked_list.click:92:9`: the `execute()` expansion in an `else`
    arm emits two `step()`s too many before its explicit `if at(...)` across
    a recursive call, and its diagnostic dumps a raw `CMemory`; (c)
    `sequence_transform.click:51:5`: a path-independent closer cannot be
    stitched into a tree whose leaves already differ; (d) mode-D residue: a
    generated `have c.model == old(c.model)` inside a match arm omits the
    entry-anchored rewrite because the certificate was searched against a
    goal with the entry model already substituted. Package T5.
18. **A pointer disequality is not decided from null-ness or separation.**
    Found by package A10 on the `Right` frame of `__rb_change_child`: the
    inner test `parent->rb_left == old` must be false, but from
    `parent->rb_left == 0` and `old != 0`, or from the sibling being a
    separately owned node, the exact condition check does not derive
    `parent->rb_left != old`. Package A11.
19. **Folding the D3 frame fails on `fact parent->left == child`.** Found by
    package A9 on the scaffold's descent: with `ctx_at(child)` exactly as
    `mdtests/resource_arm_binding_struct_base.md` declares it, `let frame =
    fold(ctx_at(root->left), { model: Context::Left(root, v, r, ctx.model) },
    { sibling: rt, up: ctx });` fails with `fold requires the instance body
    facts for the proposed fields`; bisecting the arm shows the one blocker
    is `fact parent->left == child`, even though the clause instantiates to
    `root->left == root->left`. Package A12.
20. **A pointer-typed model payload is not a memory base for ownership at
    fold.** Found by package A9: folding the frame after the cursor moves,
    with `parent` bound to the `HeapTree::Node` identity binding, fails
    with `fold requires ownership of the complete instance body` while the
    pointer equality between the binding and the cell's owner is an
    available premise; substituting a C local moves it past ownership to
    gap 19. A6 fixed payloads in propositions, not in ownership lookup.
    Package A12.
21. **Smaller scaffold-walk blockers from A9**, all pre-existing: `have
    p->left == root by simp;` does not lower ("0 paths") when `p` is a
    pointer local aliasing `root`; the selected arm's `fact p != 0` is not
    published at contract lowering (A1 published cells only, D7 says facts
    too), so `tree_leftmost`'s `if (root == 0)` needs a `branch` whose then
    arm unfolds and is infeasible; `old(t.model)` in a loop invariant fails
    with "resource instance `t` is not owned at this snapshot" once `t` was
    unfolded and refolded before the loop, while the same `old(t.model)`
    works in a `have`; a loop binder under a fresh name fails with the bare
    "could not lower entry invariants: Paths"; match-arm bindings are out
    of scope in loop clauses; and `observe` cannot name a fielded binder.
    Package A12 owns the first four; the last two are not scheduled.
22. **Separation from separate unfolds does not reach a later frontier.**
    Found by package A11: after unfolding a frame and two subtrees
    separately, the deciding context holds three single-object
    compositions rather than one merged composition, so the separation of
    two owned nodes is not projected and `parent->rb_left != old` for a
    non-empty sibling is undecided. Cross-composition separation is not
    sound to project blindly; the fix is in how ownership from separate
    unfolds is composed at the frontier. Not scheduled until C3 needs it.
23. **One audit disagreement remains after T5.** T5 fixed gap 17 (c) and
    (d) and made (a) an honest refusal; the examples audit is 401 of 457
    with the quarantined multifile-registry session failure. (b),
    `marked_linked_list.click:92:9`, is not a step-count bug as T3 guessed:
    on recheck the arm's `step()` under `RequireProven` reproves the C
    guard from the surface lowering of the condition, whose load reads the
    whole current snapshot, while the C guard evaluates against the
    snapshot its own load resolved; after the recursive call they differ
    by a cell the load cannot alias, so neither arm is excluded. The fix
    is a decided-arm step that selects the transition the arm's polarity
    already decided instead of reproving the guard, which the certificate
    vocabulary lacks. Also noted: `augment_rotate_model_callback.md`'s
    certificate relies on a case fact cited under a spelling that no
    longer lowers to it, the same class as (d), and will resurface if the
    surface-map acceptance rule is tightened. Package T6, not scheduled
    ahead of the rbtree proofs.
24. **Gaps 19 and 20 were one bug, now fixed by A12.** A proof `fold` or
    `unfold` lowered its resource arguments with the entry parameter values
    while its fields used the current locals, so inside a loop body that had
    moved the cursor `ctx_at(root->left)` named the entry root's cell. Both
    refusals were the mismatch. `lower_resource_clause_at_current_locals`
    in `resource_lowering.rs` fixes it.
25. **Gap 21's root cause: a struct-pointer local has no struct layout.**
    Found by A12: `have p->value == root->value` fails for any field, not
    only pointers, because the sidecar parser's `current_struct_params`
    comes only from `parse_parameters`; `syntax::C0Function` records
    globals, static locals, and aggregates but not automatic locals' struct
    names. The C parser must carry them through `parse_c_layouts`. A
    second, separate confusion: a `have` naming a local before the
    frontier has executed its assignment reports "0 paths" instead of
    naming the local. Package A13.
26. **Publishing the selected arm's facts at contract lowering breaks nine
    fixtures.** A12 implemented D7's fact publication and reverted it: the
    fact itself (`p != 0` for the `Node` arm) makes certification fail
    with "the checked execution started at a different entry state than
    the contract and could not be rebased onto it" in `rotation_model_preserved`,
    `resource_tree_node_init`, `rb_at_link_helpers`, `rb_ctx_change_child`,
    `resource_cross_family_children`, `resource_fields_match_memory_body`,
    `match_bindings_in_branch_arm`, `model_identity_pointer_payload`, and
    `proof_match_arm_fact_survives_sibling_write`; the contract candidates
    then carry nine resource facts against the contract's one. Package A13.
27. **A refuted arm is not published as a negative model fact.** Found by
    A12 at the very end of the scaffold's descent: the next iteration's
    `invariant sub.model != HeapTree::Empty` needs `left_model != Empty`
    from the loop guard `root->left != 0`, whose only link is `tree_at`'s
    `Empty` arm fact `p == 0`. A nested `match l.model` cannot close the
    `Empty` arm because `contradiction` needs the exact fact and its
    negation in the arm and `root->left == 0` only appears after
    `unfold(l)`; an unfolding arm becomes live and the driver declines a
    live `contradiction` arm; running the infeasible arm to the back edge
    leaves `close_invariants()` a false goal from inconsistent premises.
    This is the descent shape of every rbtree loop. The mechanism is D7
    applied to refutation: when a path fact refutes an arm's own fact, the
    folded instance's model is not that constructor, published at contract
    lowering, loop heads, and loop back edges. Package A13.
28. **Gap 23 was stale; `_Bool` and float loads are still unnamed.** T6
    bisected the last audit disagreement to A10: naming wide integer loads
    made the arm's assumed guard and the C guard the same term, so
    `marked_linked_list.click:92:9` audits clean from b0cfc0e6 on; T6 adds
    the missing regressions and tightens the stale-spelling case-fact
    acceptance to constructor equations re-lowered at the recheck state.
    The examples audit is 402 of 457: only the deferred witness refusal and
    the quarantined multifile-registry remain. Left unscheduled: a `_Bool`
    struct member breaks `unfold` of a recursive witness resource
    ("resource rewrite changed more than a definitional representation")
    because `Bool`, `Float32`, and `Float64` loads still read back as raw
    `MemoryLoad` terms; the same adoption argument as A10.
29. **An ascending walk stops at the contract boundary.** Found by A13
    after the loop mechanics worked (the loop-head refutation closes the
    `Top` arm): with `consumes t: ptree_at(p, parent); produces sub:
    ptree_at(result, ...)` the produced binder cannot reuse the name the
    loop rebinds ("duplicate resource instance binding sub"), and the walk
    has no way to rename its final instance without a fold it cannot
    perform; with `owns` on both sides the exit clause re-reads a parameter
    the loop reassigned ("could not lower resource ptree_at argument 1: the
    kernel evaluation produced 0 paths"), since a returned instance's
    arguments must be the entry-time ones. Before that, the refold of the
    parent node from the old subtree plus the sibling was unfinished
    ("loop binder sub has no owned ptree_at instance at its arguments
    here"). Every rbtree fixup loop ascends, so this blocks C3, C4's
    `rb_next`/`rb_prev`, and C5. Package A14.
30. **Smaller findings from A13, not scheduled.** A `have` whose explicit
    script fails can report only "body did not construct a completed proof
    object" with no goal or tactic (`checked_have_with_proof` returns
    `Ok(None)` on some routes); `unfold(pure_fn(...))` inside a nested
    proof `match` arm fails the same way while the enclosing arm succeeds.
    A13 also fixed a pre-existing audit defect in passing: a location-scoped
    verification planned C termination for every function in the file, so
    any file with a ranked loop failed every other claim's audit sites.
31. **Soundness hole: a `while` guard with an unevaluable conjunct drops
    it.** Found by A14, reproduced with no resources or loop binders:
    `while (a != 0 && p[0] != 0) { a = 0; }` in a function that does not
    own `p`, contracted `ensures result == 0`, verifies and audits clean
    although the loop never runs when `p[0] == 0`. The second conjunct's
    branch is dropped instead of refused and the exit assumes the negation
    of the first conjunct alone. When both conjuncts are evaluable the loop
    tactic refuses correctly. P1 regardless of rbtree. Package S1.
32. **An induction hypothesis fixes every non-inducted parameter.** Found
    by A14: `induct(ctx) as ih` yields `ih` of one argument, so the
    context-transport lemma `heap_inorder(a) == heap_inorder(b) implies
    heap_inorder(plug(ctx, a)) == heap_inorder(plug(ctx, b))` cannot be
    proved (the `Left` arm needs the hypothesis at different `a`, `b`).
    This is the shape of the rbtree fixup invariant, so it blocks the
    rotate-then-ascend fixture and C3. Package A16.
33. **A ranked loop cannot call a contract-less inline helper.** Found by
    A14: `c_verified_function_termination_rules` builds its call graph from
    verified rules only, so an inlined straight-line helper such as
    `rb_parent` is never terminating and `decreases` fails with "every
    reachable loop, recursive cycle, and callee must have a checked
    ranking proof". Every rbtree fixup loop calls `rb_parent`. Package A15.
34. **Smaller A14 findings, not scheduled.** A body that reassigns a
    parameter cannot refold its borrowed instance at the entry position
    (`fold(tree_at(old(root)), ...)` is refused; arguments are current-state
    only); the grouped driver declines a top-level `match c.model` after a
    loop while the same shape on the subtree binder works; the loop
    tactic's "requires exactly one statement successor" refusal dumps the
    raw `While` node (S1 fixes this diagnostic); the verbatim `rb_next`
    guard `while ((parent = rb_parent(node)) && node == parent->rb_right)`
    does not parse in C0 (assignment expressions), which
    kernel-scale-preprocessing owns.
35. **The parent-as-parameter spelling is unspellable for top-level
    traversals.** Found by C4: `rb_first(root)` and `rb_next(node)` have no
    C local naming the focused node's parent, and both `rb_at(p, parent)`
    (D2) and `ctx_at(child, parent, root)` (amended D3) need it in every
    loop binder and every `produces` clause; pure functions cannot return
    pointers (gap 8) and `exists` cannot bind a `produces` argument. A13
    keyed the scaffold frame by the child alone because `tree_at(p)` takes
    no parent. Decision: re-key the rbtree model by node with the parent as
    a model payload, `RbTree::Node(identity, parent, color, left, right)`,
    the node's own arm stating its parent word from the payload, and a
    child's parent tied to `p` by a pure `int32` predicate over the child's
    model (`rb_parent_is(left_model, p) == 1`); the frame becomes
    `ctx_at(child, root)` with the parent in the `Left`/`Right` payload.
    This is a spelling change within D1 to D3. Package C1b re-spells C1,
    A14's rbtree ascent, and C4's replacement, and delivers the traversal
    descents.
36. **A `while` guard with two evaluable conjuncts is refused.** After S1,
    `while (a != 0 && p[0] != 0)` with both operands readable still refuses
    with "requires exactly one statement successor, got 2": the `loop`
    tactic certifies one successor and a conjunctive guard has two exit
    paths. The verbatim `rb_next` ascent `while ((parent = rb_parent(node))
    && node == parent->rb_right)` has this shape (once the assignment
    expression is handled by the preprocessing issue). Package A17.
37. **Proof-shape limits met by C4.** Four nested proof `match` scrutinees
    are declined ("proof-shape limitation") while three work; refolding a
    child after the inlined `rb_set_parent` needs the arm fact `((old & 1)
    | address(new)) & 1 == color_bit(color)`, which `fold` requires
    exactly and `simp` cannot close for a child named only by
    `victim->rb_left` (`have` lowers to three paths); a loop inside a
    `static inline` helper cannot be addressed from a contracted wrapper
    (`step()` executes the whole inlined call). Package A17 owns the first
    two; the third is not needed for the Linux functions, which are
    top-level.
38. **Gap 37 (b) was misdiagnosed; the blocker is load identity across an
    unfold.** A17 showed the bit-mask arithmetic already closes when the
    children are contract instances; it fails when the children come from
    `unfold(t) as { left: l, right: r }`: the child's cell is named through
    a symbolic pointer and the C's own read of the same cell in the same
    epoch mints a second load variable, and the fold's exact check has no
    route between `V_u & 1 == color_bit(lc)` and the goal over `V_c`. The
    two are related only by a pointer equality. Equating two registered
    loads at provably equal pointers in one epoch inside the exact check is
    the load-equality prover deliberately kept out of the kernel; the fix
    belongs on the surface, as an explicit step that names the identity
    (`rewrite` of the load through the pointer equality, or `normalize()
    using` the equality) and a kernel rule that accepts it as one
    certified step. Package A18. C4's general-children `rb_replace_node`
    and every fixup that unfolds a child then writes its word depend on it.
39. **A guard prefix does not publish the read authority common to the
    arms it leaves possible.** A17: the verbatim `rb_next` guard `parent !=
    0 && node == parent->rb_right` is undecided at a loop head because
    `parent->rb_right` is owned by the folded `ctx_at` frame and no single
    arm is selected; the first conjunct refutes `Top`, and both remaining
    arms own `parent->rb_right`. D7 extension: after a guard prefix, publish
    as views the cells owned by every arm still possible. Package A19.
40. **Smaller A17 findings, not scheduled.** Two ascent loops in one
    function fail the second loop's `close_invariants` with plain guards
    (pre-existing); `simp` cannot use a loop's exported exit disjunction by
    itself because the fact is kernel-minted with no surface spelling
    (`cases(...)` works); the S1 successor-refusal diagnostic no longer has
    a reachable shape.
41. **Soundness hole 2, closed by C1b: capture in pure-function unfold.**
    `unfold(f(args))` substituted arguments and then reduced the body's
    `match`, capturing a match-arm binding that shared a name with a
    parameter, so `unfold(reparent(Node(node, node, ...), parent))`
    produced the old parent and a false equation closed under `requires
    node != parent`. `prepare_contract_match_arm` now renames the binding
    out of the way (regressions `spec_function_arm_binding_capture*.md`).
42. **A body fact applying a pure predicate to a pointer is not discharged
    at fold.** C1b: `fact rb_parent_is(left_model, p) == 1` makes every
    fold refuse although the identical proposition is an available checked
    fact just before; `fact color_bit(color) >= 0` discharges, and even the
    constant `rb_parent_is(RbTree::Empty, identity) == 1` does not. So
    parent/child consistency is stated in contracts, not in the body,
    which deviates from D2. Package A20.
43. **A frame's identity payload does not stand for the C local that names
    the same node on unfolded cells.** C1b: `rb_replace_node`'s non-root
    frame fails with "requires exactly one statement successor, got 2"
    because `unfold` binds the frame's `identity` freshly and the inlined
    `__rb_change_child` reads `parent->rb_left` while the frame owns
    `identity->rb_left`; the re-keyed ascending walk has the same problem
    at its exit refutation (`fact parent != 0` no longer names the C local),
    so `rb_ascending_walk_to_root.md` stays on the parameter spelling. The
    bridge exists: `requires t.model == rb_reparent(t.model, parent)` plus
    `extract` yields `identity == parent` in the arm; what is missing is
    that equality reaching the unfolded frame's owned cells and guards.
    Package A20.
44. **Two `RbTree` shapes.** `examples/rbtree-model` (C2) still has the
    four-payload `Node`; the rbtree fixtures now use the five-payload
    re-keyed one. Package C2b ports the pure library. The verbatim `rb_next`
    guard does not parse in C0 (assignment expression;
    kernel-scale-preprocessing) and is pinned as
    `mdtests/rb_next_conjunctive_guard.md`.

## Design decisions

These are settled. A package that finds one of them unworkable stops and
reports rather than substituting a different design.

**D1. Model shape.** One `spec enum` per structure, carrying node identity as
a pointer payload, the payload the structure needs, and the submodels. For
the scaffold that is the landed `HeapTree::Node(struct tree_node*, int,
HeapTree, HeapTree)`. For rbtree it is
`RbTree::Empty | RbTree::Node(struct rb_node*, Color, RbTree, RbTree)` with
`spec enum Color { Red, Black }`. Pointers stay pointers: models grant no
ownership and are never converted to integers. In-order node identity is the
derived `List<struct rb_node*>` from a pure `inorder` function; node-set and
multiplicity claims are stated about that list.

**D2. Parent pointers and color live in the node's own arm.** The tree
resource takes the parent as a parameter, `rb_at(p, parent)`, and its `Node`
arm owns `p->__rb_parent_color` and states the packed word. C1 landed it as
two facts, `p->__rb_parent_color == address(parent) + (p->__rb_parent_color
& 1)` and `(p->__rb_parent_color & 1) == color_bit(color)`, because the
single fact with an opaque `color_bit(color)` carries no bound for the
tag-clearing step in `rb_parent`. Children
are `owns left: rb_at(p->rb_left, p)` and `owns right: rb_at(p->rb_right, p)`.
Parent/child consistency is therefore a body fact, not a separate claim, and
no witness inside a matched body is required. Acyclicity is inherent in a
finite inductive model over linearly owned nodes. The root cell
`root->rb_node` is owned by the context's `Top` frame (D3), with the root's
parent word stating a null parent.

**D3. Bottom-up algorithms use a context (zipper) resource.** Linux insert
and erase start at a node and climb parent links. The proof state holds the
ancestors as a linear stack of frames:

```click
spec enum Context {
    Top,
    Left(struct rb_node*, Color, RbTree, Context),
    Right(struct rb_node*, Color, RbTree, Context),
}

resource ctx_at(child: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => { owns root->rb_node; fact root->rb_node == child; },
        Context::Left(parent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_right, parent);
            owns up: ctx_at(parent, root);
            fact parent != 0;
            fact parent->rb_left == child;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(...) => { /* mirror */ },
    }
}

function plug(ctx: Context, sub: RbTree) -> RbTree decreases ctx { ... }
```

`plug` rebuilds the whole model from a context and the focused subtree.

Amendment after C1 (2026-09-12): the frame takes the focused child's parent
as a resource parameter, `ctx_at(child, parent, root)`, exactly as `rb_at`
takes it. `Top` states `parent == 0`; `Left(grandparent, color,
sibling_model, up_model)` owns `parent`'s cells and `up: ctx_at(parent,
grandparent, root)`. A frame keyed only by the child needs a pure accessor
from `ctx.model` to the parent pointer in its contracts, and pure functions
cannot return pointers (gap 8); with the parent as an argument, contracts
and loop binders name it as the C local the Linux loops already maintain
(`parent = rb_red_parent(node)`), and no accessor is needed. C1's fixtures
use concrete frames and predate this amendment; C3 adopts it.
Every loop invariant in the rbtree algorithms has the form
`inorder(plug(ctx.model, sub.model)) == inorder(old(t.model))` plus the
algorithm's shape predicate. `ctx_at` contains `rb_at`; `rb_at` never contains
`ctx_at`, so the mutual-recursion rejection is untouched. The scaffold uses
the same construction without color or the root struct.

**D4. Contract interface for bottom-up entry points.** `rb_insert_color`,
`__rb_erase_augmented`, and `____rb_erase_color` are contracted over a context
plus focused subtree at the given node, not over a whole tree plus a
membership witness. A top-down tree cannot locate an arbitrary member
without a path, and insert callers build the context in their own descent
loop anyway. Whole-tree wrappers relate `ctx_at(node, root)` and
`rb_at(node, parent)` to the entry model through `plug`. The consequence for
callers of the verified erase is documented, not hidden.

**D5. Loop binders reuse the contract binder syntax.** A loop header may
declare `owns name: resource(args);`. Semantics mirror a callee contract:

- `initialize` consumes the unique enclosing owned instance whose family and
  arguments match, and binds `name`. Ambiguity is an error. No binder map in
  the first slice.
- The body holds `name`; invariants read `name.field`; unfold and fold work
  as in any proof. Undeclared instances are unavailable in the body and
  returned after it, which is the existing exclusive-instance rule.
- `close_invariants()` selects the instance the same way with the arguments
  re-evaluated in the current state, rebinds `name` to it whatever the body
  called it, and checks the invariants against its fresh fields. This is what
  lets a body hand a child `l` to the next iteration: after `root =
  root->left`, `l` is `tree_at(root)` by proved argument equality.
- After the loop, `name` denotes the final instance at the final arguments.
- A loop name may reuse an enclosing binder name; that is a rebinding.
  `old(name.field)` keeps its meaning, the function-entry instance of the
  function-level binder. No loop-entry snapshot in the first slice.
  Landed behavior (A3): a loop binder takes the unique owned instance of its
  family with provably equal arguments and renames it, so a fresh name
  consumes the enclosing name for the rest of the function and cannot appear
  in `ensures`; reuse the enclosing name. The head gives the binder fresh
  fields, so its model at the head is exactly what the invariants state.

**D6. Structural loop measure is `decreases name;` with no keyword.**
Functions and resources share one namespace (declaring both is rejected), so
`decreases` measures are parsed as one expression and classified after
resolution: an integer expression, a resource application such as
`list(node)`, a loop or contract binder such as `sub`, or an ADT parameter in
a pure function. The existing `decreases resource list(node)` spelling is
replaced by `decreases list(node)`; `src/surface/parser.rs` currently
branches on the `resource` keyword before resolution and stops doing so. The
back-edge rule is the function-level one: the instance rebound to the name
must be a direct contained child, in the exact resource definition, of the
instance the name held at the loop head, checked from the unfold that
exposed it. Descending loops decrease `sub`; ascending and
rotate-then-ascend loops decrease `ctx`, because a rotation may grow the
subtree but the context strictly loses a frame.

**D7. Arm selection from requirements, one mechanism for contracts and loop
heads.** When a section's requirements together with constructor
exhaustiveness entail exactly one arm of a matched instance, lowering
exposes that arm's cells as read authority and its facts as assumptions,
with the arm's bindings as fresh symbolic values. `c.model != None` on a
two-constructor enum and `exists (v) { c.model == Some(v) }` both select
`Some`. If no single arm is entailed, the composite stays folded and reads
through it fail as today; there is no implicit proof by cases. The same
decision applies at a loop head, where the invariants play the role of the
requirements, so a guard such as `root->left != 0` can read through the
focused subtree. This generalizes the existing decidable-guard expansion in
`src/kernel/functions.rs` (`expand_decidable_composite_resource_frontier`)
rather than adding a second path. No sugar such as `requires c.model is
Some` in this issue.

**D8. Matched arms may own children of another declared resource.** The
same-family restriction in `algebraic_types.rs` is lifted. Child field
equations, the explicit child map on fold, `unfold ... as { }` naming, and
the acyclicity check across definitions all apply unchanged. Mutual
resource-definition cycles remain rejected.

**D9. No new resource algebra and no automatic unfolding.** No ghost state,
fractions, magic wands, or `auto` fold search. Every layer a proof needs is
named. Reasoning and certificates stay output-sensitive in the explicitly
exposed model terms; each rebalancing case is an explicit sequence of
unfold, C steps, fold, and `have`. Symmetric cases are written out; proof
reuse across mirrored cases is not a goal of this issue.

**D10. Pure library.** `inorder`, membership, `black_height` over `Nat`,
`is_rb`, and the almost-red-black predicates for insert (one red-red
violation at the cursor) and erase (one black deficit at the cursor) are
pure functions and predicates with induction theorems. Rotation, splice, and
recolor lemmas are stated over models and proved once; C proofs apply them.

**Deferred language questions.** Decided 2026-09-11 to add no language
beyond D5 and D6. The following stay out of scope for every package here:
resource-transforming lemmas (which would give a reusable "focus the tree at
a member" step and proof reuse across mirrored cases), a binder map on loop
headers, loop-entry snapshots such as `at(loop.entry, sub.model)`, and a
positive constructor test such as `requires c.model is Some`. A package that
appears to need one reports the need instead of adding it.

## Progress

- 2026-09-11: A1 (arm selection, dff4ebdc), A2 (cross-family arm children,
  de1da207), A3 (loop binders, 9e62f2a2), A5 (struct-pointer arm bindings
  as memory bases, 036170c4), B2 and B3 (right rotation, membership,
  negative rotations, 688e7990) are on master. A5 resolves arm binding
  types with a bounded pre-scan of `spec enum` declarations in the parser
  rather than a declaration-order rule. A4 and A6 are in progress; C1 and
  C2 are dispatched. `tree_contains` verifies model preservation only
  until A6 lands its membership postcondition.
- 2026-09-12: A6 (pointer payloads and arm scoping, 7b52373a) and C2 (the
  pure red-black library in `examples/rbtree-model`, c9d5afee) are on
  master. `tree_contains` proves the guarded membership form; the
  unguarded form is package A7. A4, A7, and C1 are in progress.
- 2026-09-12: C1 (`rb_at`, `ctx_at`, `plug`, the seven link helpers and
  `__rb_change_child` on verbatim Linux bodies, 05257e8e) is on master. A7
  is gating; T1 (audit defect) and A8 are dispatched; A4 is in progress.
- 2026-09-12: A7 (`let r = step(...)` names a call's scalar result when the
  callee produces no instance, 9c7710ee) is on master; `tree_contains`
  verifies the unguarded membership postcondition. T2 dispatched.
- 2026-09-12: A4 (`decreases <expression>` classified after resolution,
  matched bodies as structural children, loop back-edge rule, head-time
  binder arguments, arm views at loop heads, 2ab5dba3) is on master with a
  confirming full gate; its positive loop fixtures wait on A9. T1 (audit on
  an infeasible `branch` arm, fixed by expanding the dropped arm's tactic by
  removal, 531b5651) is on master; the scaffold audits 26 of 26 sites. T3
  dispatched for gap 14; T2 is gating.
- 2026-09-12: A8 (proof `match` of any width, with excluded arms grouped
  correctly, 590b2553) and T2 (bounded failed-`simp` diagnostic, 92a81e32)
  are on master with a confirming full gate; A8 found gaps 15 and 16. A9
  and A10 are dispatched; T3 is in progress.
- 2026-09-12: T3 (three audit modes fixed: post-exit `have` in an open
  scope, scope `have` expansion recording, `assumption` closing a produced
  resource claim; bb009743) is on master. T5 dispatched for the residue.
- 2026-09-12: A10 (wide integer loads named by their load variable, so a
  frame's unwritten facts survive a sibling write; one contract over the
  `Top` and `Left` frames of `__rb_change_child`; b0cfc0e6) is on master
  with a confirming full gate. A11 dispatched for gap 18. A9 and T5 are in
  progress.
- 2026-09-12: A9 (proof `match` at loop-body frontiers and after C steps,
  `is_recursive` unified) is green and rebasing; the scaffold walks it was
  to deliver are blocked by gaps 19 to 21, now package A12, which
  dispatches when A9 lands.
- 2026-09-12: A9 (66bd8005) is on master. A12 dispatched; A11 and T5 in
  progress.
- 2026-09-12: A11 (pointer disequality from null-ness or separation, with
  the verbatim `__rb_change_child` `Right` frame verified and audited on a
  general frame; ec8ffc4a) is on master. Its nested-match finding predates
  A9 and should be re-checked.
- 2026-09-12: T5 (2cb5669f) is on master; examples audit 401 of 457 with
  one real disagreement left (gap 23, package T6). A12 in progress.
- 2026-09-12: A12 (0e7d8000) is on master: proof folds read their
  arguments at the current cursor (gaps 19 and 20), and a fresh loop binder
  is refused by name. The descent reaches `close_invariants()` and stops
  on gap 27. A13 dispatched; T4 and T6 in progress.
- 2026-09-12: T4 (63ec6190) is on master: a wide execution join distributes
  a deferred `if` only into the arms its split selects and certificates
  are shared `Arc` vectors, so the retained certificate is linear in width
  and a 32-arm match verifies in 0.8 s instead of 9.3 s. Two notes, not
  scheduled: the deterministic tactic-work counter does not observe
  certificate assembly, so `click profile` could not point at this class
  of cost; and a generated 44-arm match declines to verify on a bound T4
  did not identify.
- 2026-09-12: T6 (2ed15042) is on master; gap 23 closed as stale (gap 28).
  All tooling packages T1 to T6 are landed. A13 in progress.
- 2026-09-12: A13 (6335d1eb) is on master: refuted arms publish negative
  model facts at unfold, loop head, back edge, and contract lowering; the
  selected arm's facts are published at contract lowering; struct-pointer
  locals have layouts; `old(name.field)` in a loop invariant reads the
  entry instance. **B1's core is delivered**: the unchanged `tree_leftmost`
  and `tree_rightmost` verify and audit (35 of 35 sites) with `Context`,
  `ctx_at(child)`, `plug`, loop binders, a loop-body `match`, and
  `decreases t;`. A14 and C4 dispatched.
- 2026-09-12: A14 (660c7643) is on master: ascending walks verify and
  audit on the scaffold and the rbtree shapes; a resource argument may be
  the null constant, and a loop exit publishes refuted arms. No binder
  renaming rule was needed. It found the soundness hole (gap 31), the
  induction-hypothesis limit (gap 32), and the inline-helper termination
  gap (gap 33); S1, A15, A16 dispatched, C4 in progress. C3 waits on A15
  and A16.
- 2026-09-12: A15 (819cb5b1) is on master: inlined helpers are call-graph
  nodes for termination, and a sidecar-contracted inline helper with its
  own ranked loop is keyed by its executing name. Two notes, not
  scheduled: a contract-less inline helper that contains a loop cannot be
  proven at all today (the caller's `execute()` has no loop region for it,
  so a symbolic argument unrolls until the budget is exhausted), and the
  termination SCC step runs a reachability query per ordered function pair,
  quadratic in function count, which a kernel-scale import would hit.
- 2026-09-12: A16 (24517c61; `ih` over all theorem parameters,
  `plug_inorder_transport` verifies), S1 (841126d4; the while-guard
  soundness hole closed in `assume_condition_truthiness` with six failing
  regressions, no fixture relied on it), and C4 (32992501; `rb_replace_node`
  for a childless victim on the verbatim body) are on master. C4's
  traversal functions are blocked by gap 35; C1b and A17 dispatched. C3
  waits on C1b and A17.
- 2026-09-12: A17 (1472f6f8) is on master: every exit of a short-circuit
  guard is certified and joined, and proof nesting goes from an effective
  five levels to eleven. Its masked-word part was a misdiagnosis (gap 38);
  A18 and A19 dispatched. C1b in progress.
- 2026-09-12: C1b (368c4aec) is on master: the rbtree model is keyed by
  node with the parent in the payload; **the unchanged Linux `rb_first`
  and `rb_last` verify and audit** (19 of 19 sites), with the seven link
  helpers, `__rb_change_child` in all three frames, and `rb_replace_node`
  at the root; soundness hole 2 closed. C2b dispatched; A20 after A18.
- 2026-09-12: A19 (eec257aa) is on master: the cells every possible arm
  owns are published as views at contract lowering, loop heads, and per
  guard conjunct; the translated `rb_next` ascent guard verifies and
  audits on the parameter spelling. A18 and C2b in progress.

## Work packages

Dependencies are stated per package; everything else may run in parallel.
Each package lands as one coherent green commit with its focused regressions
and documentation, judged by `scripts/check.sh`'s exit status. Existing C
sources are fixed; adaptation goes into contracts, resources, lemmas,
lowering, or the kernel. No package creates issues. A package that hits a
tooling failure listed in `AGENTS.md` stops and reports.

### Phase A: verifier extensions

**A1. Arm selection at contract lowering and loop heads (D7).**
Scope: surface lowering and the kernel's decidable-frontier expansion.
Regressions: the `cell` reproduction from gap 2 as a positive mdtest in both
spellings; a three-constructor enum where `!= X` does not select an arm and
is refused with a diagnostic naming the instance; the original finding, with
`mdtests/augment_rotate_model_callback.md`'s `rotate_left` recontracted as
`consumes t: tree_at(node); produces r: tree_at(result); owns
node->augmented; owns node->right->augmented;`; a loop-head guard reading
through a focused modeled instance once A3 lands. Out of scope: proof by
cases, new proposition forms. No dependencies; the loop-head regression is
added when A3 is available.

**A2. Cross-family children in matched arms (D8).**
Scope: `src/surface/validation/algebraic_types.rs` and any lowering that
assumed the child family equals the parent's. Regressions: a two-family pair
where a frame resource owns a `tree_at` sibling and a same-family `up` child,
with fold, `unfold ... as`, and refold; a negative where the child family is
undeclared; a negative where the child map names an instance of the wrong
family; confirmation that a two-definition cycle is still rejected. No
dependencies.

**A3. Loop binders `owns name: resource(args);` (D5).**
Scope: loop-header parsing, `loop_resource_declarations` in
`src/surface/lowering/annotations.rs`, and the kernel's `close_invariants`
and loop-exit binding in `src/kernel/loops.rs`. Regressions: the `counter`
loop from the design discussion (`bump_n`, invariant `c.count ==
old(c.count) + i`, refold each iteration); rebinding by argument equality
where the body folds under a different name; negatives for an ambiguous
instance at `initialize`, a missing instance at the back edge, an invariant
reading an undeclared binder, and a body writing through an undeclared
instance. Update `docs/concepts/loops-and-invariants.md` and the language
reference. No dependencies.

**A4. Structural measure `decreases name;` for loops and fielded resources (D6).**
Scope: parse `decreases` as one expression and classify after resolution;
extend `structural_resource_children` so a matched body's named arm children
are structural children (gap 7), for the existing function-level rule and
the new loop back-edge rule alike; loop back-edge ancestry check reusing the
function-level checker; migrate the `decreases resource` spelling in fixtures
and docs. Also finish D5's argument rule, which A3 left at the existing
loop-resource convention: loop-binder arguments are evaluated once at loop
entry, so `owns sub: tree_at(root);` over a body that assigns `root =
root->left` fails the back-edge comparison. The head must build its declared
instance at the havocked arguments and the back edge must re-evaluate them
in the current state (`loop_body_resource_context` and
`rebind_loop_binder_instances` in `src/kernel/loops.rs`). First
regressions: the scaffold's recursive `tree_contains` with `decreases t;`
on its `owns t: tree_at(root)` binder, and a descending loop whose binder
argument is the reassigned cursor. Also restore `return node->value;` in
`mdtests/loop_owns_modeled_instance.md`, which A3 changed to `return i;`
because arm selection at a loop head was not yet available. Regressions: the
three loop shapes from
[structural-loop-termination.md](structural-loop-termination.md) on the
scaffold (descend to leftmost, ascend through a context, rotate then
ascend), with negatives for staying on the same node, moving to an unrelated
node, and refolding a consumed frame. Depends on A3; the ascending shapes
depend on A2 and B1's context definition. Closes the loop-termination issue
when its acceptance criteria are met.

**A5. Struct-pointer constructor bindings as memory bases in arm bodies.**
Scope: carry the struct name on a spec-enum field of struct-pointer type and
make matched-arm bindings of that type usable as struct bases in the arm's
`owns`, `fact`, and child-argument clauses. Declaration order does not create
scope (see `docs/reference/language/grammar.md`), so resolve the binding
types in a pass that has the datatype available rather than adding an order
rule. Regressions: the D3 frame `ctx_at(child)` whose `Left(parent, value,
sibling_model, up_model)` arm owns `parent->value`, `parent->left`,
`parent->right`, `sibling: tree_at(parent->right)`, and `up: ctx_at(parent)`
with `fact parent->left == child`, folded, unfolded with `as { ... }`, and
refolded; a negative where a binding of non-struct-pointer type is used as a
base; a negative where the binding's struct has no such field. Depends on
A2. B1 and C1 depend on it.

**A6. Pointer payloads and arm bindings in propositions.**
Scope: let a pointer-typed constructor binding or pure-function result be
compared with a C pointer in `have`, `ensures`, `normalize() using`, and
`rewrite`, bridged by the resource fact `p == identity`; keep match-arm
bindings in scope inside nested `branch` and proof `if` arms and inside a
`have` that also mentions C variables. Regressions: the scaffold's
`tree_contains` with `ensures result == heap_member(old(t.model), target)`
(B2 left the partial contract in place); a small mdtest equating a
`Node` identity binding with a parameter under `fact p == identity`; a
negative where the pointers are provably different. No new syntax: this is
lowering and kernel scope. Depends on nothing; C4 and the B2 membership
result depend on it.

**A7. Name a call result used directly in a condition.**
Scope: let a proof refer to the scalar result of a C call that appears only
inside a condition or return expression (gap 9), for example through the
existing `let r = step(call, {...})` binder form applied at that frontier,
or through the postcondition being available on the branch fact by the
call's result identity. Regression: the scaffold's `tree_contains` with the
unguarded `ensures result == heap_member(old(t.model), target)`, and a
small fixture with `if (f(x)) return 1;`. No new syntax if the `let ... =
step(...)` form suffices. Depends on A6.

**T1. Make `click audit` agree with `click verify` on nested arm tactics.**
Scope: reduce gap 11, fix the grouped-proof source-tactic indexing for
`branch`/`if` arms, and add audit coverage of the reduction (and of the
scaffold if cheap) to the gate. No proof or C changes to route around it.

**A8. Lift the two-constructor cap on proof `match`.**
Scope: remove the stale guard in `match_cases.rs` if the range split
already handles wider joins, or implement the wider join; regressions with
a three- and a four-constructor execution `match`, including an all-but-one
contradiction shape and a negative missing arm. Depends on nothing; C3
depends on it.

**T2. Bound the failed-`simp` diagnostic.**
Scope: replace the repeated Rust debug dump of the proposition and
algebraic schemas in a failed pure `simp` with the bounded goal, premise,
and search context the diagnostics policy allows. Regression: a fixture
whose failure message is checked for the absence of the debug dump.

**T3. Make `click audit` agree with `click verify` across `examples/`.**
Scope: run the audit to completion, reduce each failure mode of gap 14,
fix it in expansion, and add `verify -> expand -> reverify` regressions per
mode. No proof or C changes to route around.

**A9. Proof `match` on an instance model at any execution frontier.**
Scope: let `match name.model { ... }` run at a loop-body frontier and after
C steps, not only at unchanged function entry, introducing each arm's
constructor equation and bindings on that arm's path with the same range
split the entry form uses (coordinate with A8's arity change in
`match_cases.rs`; land after it). With that, `unfold(sub) as { ... }`
inside `preserve` has its constructor. Regressions: A4's missing loop
shapes on the scaffold and small fixtures: a descending loop to the
leftmost node with `decreases sub;`, an ascending loop through
`ctx_at(child, parent, root)` frames with `decreases ctx;`, a
rotate-then-ascend loop, and the negatives for an unrelated node and a
refolded consumed frame. Also flip or bypass `is_recursive` for matched
recursive definitions consistently (A4 bypassed it in
`structural_resource_children` only). No new syntax. Depends on A4 and
A8; B1 and C3 depend on it.

**A10. Keep an arm's unwritten-cell facts across a sibling write.**
Scope: reduce gap 16, find why the arm's body facts about cells the
execution did not write are not carried to the post-write fold when the arm
was introduced by a proof `match` rather than a contract requirement, and
fix it in the match-arm path (likely where the arm's facts are recorded as
path premises versus contract assumptions). Regressions: the reduction as a
positive; the same with the fact genuinely invalidated by the write as a
negative. Depends on A8; C3 and C5 depend on it.

**A11. Decide `p != q` from `p == 0` and `q != 0`, and from separation.**
Scope: a bounded derived pointer fact in the exact condition check and in
`simp`/`normalize`, keyed by the pointers involved. Regressions: the two
null-ness reductions, a negative with neither pointer known non-null, the
separation case, and the `Right` arm added to
`mdtests/rb_ctx_change_child_one_contract.md` so one contract covers all
three frames. Depends on A10; C3 and C5 depend on it.

**A12. Unblock the scaffold walks (gaps 19, 20, 21) and deliver B1's core.**
Scope: fix the fold body-fact check for a clause that instantiates to a
reflexive equality through a struct-pointer binding (gap 19); let a
pointer-typed payload binding resolve ownership at fold when it is
provably equal to the owner (gap 20); lower a `have` over an aliasing
pointer local; publish the selected arm's facts at contract lowering as
D7 states; make `old(name.field)` in a loop invariant read the function
entry instance regardless of intervening unfold/refold; and name the
refusal for a fresh loop binder. Acceptance is B1's core: the unchanged
`tree_leftmost` and `tree_rightmost` verified and audited on
`examples/modeled-binary-tree` with `Context`, `ctx_at(child, parent)`,
`plug`, loop binders, a loop-body `match`, and `decreases sub;`, plus the
ascending and rotate-then-ascend fixtures and the two context negatives
A4 and A9 could not land. Depends on A9. B1 then only adds the README and
docs.

**A13. Complete the descent (gaps 21, 25, 26, 27, and blocker 5).**
Scope, in this order: (1) publish a refuted arm as a negative model fact
per gap 27, using `select_resource_model_arm`'s evidence index in reverse,
at contract lowering, loop heads, and back edges; (2) make the selected
arm's facts publishable at contract lowering by finding why an extra
section assumption changes the certified entry state (gap 26), so the
contract and the checked execution agree; (3) carry struct-pointer locals'
struct names through the C parser so field places on locals have layouts
(gap 25), and name the local in the "before its assignment" `have`
refusal; (4) `old(name.field)` in a loop invariant after an unfold and
refold before the loop. Acceptance is unchanged from A12: the scaffold's
`tree_leftmost` and `tree_rightmost` verified and audited with `Context`,
`ctx_at(child)` keyed by the child with the parent in the payload for this
C (A12's parent-naming decision; D3's two-argument frame stays for the
rbtree, whose loops have a `parent` local), `plug`, loop binders, a
loop-body `match`, and `decreases sub;`, plus the ascending and
rotate-then-ascend fixtures and the two context negatives. Depends on
A12.

**A14. Ascending and rotate-then-ascend walks (gap 29).**
Scope: let a `produces` binder at the exit take the name the loop rebinds
(or let the loop's final instance be renamed at the boundary), evaluate a
returned `owns` instance's arguments at entry when the parameter was
reassigned, and finish the refold of a parent node from its old subtree and
sibling inside an ascending `preserve`. Acceptance: an ascending walk over
`ptree_at(p, parent)`/`pctx_at(child, parent)` frames with `decreases
ctx;`, verified and audited; a rotate-then-ascend loop that folds a rotated
subtree and continues at the parent frame; and the same on the rbtree
shapes `rb_at(p, parent)`/`ctx_at(child, parent, root)` with a verbatim
`rb_next`-style ascent. Depends on A13; C3, C4's ascending half, and C5
depend on it.

**S1. Refuse an unevaluable guard conjunct (gap 31).** Scope: an
unevaluable guard operand makes the guard undecided and refuses, never
drops a branch; audit every condition shape; failing regressions per
shape; bounded diagnostic for the successor refusal. Soundness: lands
ahead of everything.

**A15. Ranked loops may call contract-less inline helpers (gap 33).**
Scope: classify an inlined helper in the termination call graph by its
body (straight-line is terminating; a loop needs its own ranking; a
recursive helper needs a rule), bounded to the body. Regressions: A14's
`rb_ascending_walk_to_root.md` with `decreases`, a numeric case, and
negatives. C3 and C5 depend on it.

**A16. Induction hypotheses over all theorem parameters (gap 32).**
Scope: `ih` takes the theorem's full parameter list, the inducted position
accepting a strict structural descendant and the others any well-typed
term, with the theorem's `requires` checked at the instance. Regressions:
`plug_inorder_transport` on the scaffold, a two-parameter list theorem,
negatives for a non-descendant and a violated premise. C3 depends on it.

**C1b. Re-key the rbtree model by node (gap 35).** Scope: `rb_at(p)` with
`RbTree::Node(identity, parent, color, left, right)`, `ctx_at(child,
root)` with the parent in the frame payload, `rb_parent_is`, `plug`; re-verify
C1's link helpers and `__rb_change_child`, A14's ascending walk, and C4's
`rb_replace_node` on the new spelling (old fixtures replaced, not kept in
parallel); then the unchanged `rb_first`, `rb_last`, and the descending
half of `rb_next`/`rb_prev`, with results stated through `rb_inorder`.
Depends on A14, A15, C4. C3 and C5 depend on it.

**A17. Conjunctive loop guards and deeper proof shapes (gaps 36, 37).**
Scope: let the `loop` tactic certify a guard with several exit paths
(each exit path assumes its own conjunct's negation and the earlier
conjuncts' truth), so `while (a && b)` verifies without a C rewrite; lift
the three-scrutinee nesting limit on proof `match`; and make a bit-masked
parent-word fact closable after `rb_set_parent` for a child named through
a field path. Regressions: a two-conjunct guard loop, a four-level match,
and C4's general-children `rb_replace_node`. C3's ascent depends on the
guard part; C1b's `rb_next` ascent depends on it too.

**A18. Load identity across an unfold (gap 38).** Scope: a surface step
that equates a load variable minted by C execution with the load the
unfolded child's body named for the same cell, justified by the pointer
equality the context holds, checked by the kernel as one bounded step
(no search in the exact check). Regressions: A17's `sp7` reduction and
C4's general-children `rb_replace_node`. C3 and C5 depend on it.

**A19. Read authority common to the possible arms (gap 39).** Scope:
after a guard prefix or a section requirement refutes some arms of a
folded matched instance, publish as views the cells every remaining arm
owns, at contract lowering, loop heads, and within a guard's own
short-circuit evaluation. Regression: the verbatim `rb_next` ascent guard
on the re-keyed frame. C1b's `rb_next` and C3's fixup guards depend on
it.

**A20. Pointer-argument body facts and payload-to-local identity (gaps 42,
43).** Scope: make a body fact applying a pure function to a pointer
argument dischargeable at fold exactly as a scalar one; and let a proved
equality between a frame's identity payload and a C local (`identity ==
parent`) apply to the unfolded frame's owned cells and to guard reads, so
`rb_replace_node`'s non-root frames and the re-keyed ascent verify.
Regressions: `rb_parent_is` as a body fact; `rb_replace_node` `Left` and
`Right` frames; `rb_ascending_walk_to_root.md` ported to `rb_at(p)`/`ctx_at`.
Depends on A18 (same fold check). C3 depends on it.

**C2b. Port the pure red-black library to the re-keyed model.** Scope:
`examples/rbtree-model` on `RbTree::Node(identity, parent, color, left,
right)`, keeping every theorem, and adding the parent-consistency predicate
and its preservation by rotation and recolor. Fixtures only. C3 depends on
it.

**T4. Make wide execution joins linear.**
Scope: profile the frontier split and join path on the N-arm match and
nested `branch` fixtures from gap 15, remove the deep clones or make them
share structure, and add a deterministic scaling regression over several
widths per `docs/internals/verification-efficiency.md`. Not on the rbtree
critical path; schedule after the Phase A packages.

**T5. Close the remaining audit disagreements (gap 17 b, c, d) and refuse
(a) with a real diagnostic.** Scope: the `execute()` step-count expansion
across a recursive call, the multi-leaf closer stitching, and the
`old(...)` anchoring of match-arm certificates; make expansion refuse a
witness it cannot spell instead of emitting unparseable text; replace the
raw `CMemory` dump. Regressions per mode as `verify -> expand -> reverify`
tests. Depends on T3.

**T6. Decided-arm step on recheck (gap 23).** Scope: let a rechecked
`branch`/`if` arm select the C transition its polarity decided rather than
reprove the guard against a differently resolved snapshot; then revisit the
stale-spelling case-fact acceptance so `augment_rotate_model_callback.md`
does not depend on it. Depends on T5 and A9.

### Phase B: models on the fixed scaffold

**B1. Context resource, `plug`, and the iterative walks (D3).**
Scope: `examples/modeled-binary-tree` sidecar. Add `Context`, `ctx_at`,
`plug`, and verify the unchanged `tree_leftmost` and `tree_rightmost` with
`produces ctx: ctx_at(result); produces sub: tree_at(result); ensures
plug(ctx.model, sub.model) == old(t.model);` and the leftmost or rightmost
position stated on the model. Regressions: the example itself plus a focused
mdtest with a negative that drops a frame. Depends on A1, A2, A3, A4, A5, A9.

**B2. Right rotation, membership, and rotation theorems.**
Scope: `heap_rotate_right` with its in-order preservation theorem, the
unchanged `tree_rotate_right` contracted like the left rotation, a pure
`heap_member` with the theorem that membership is list membership of
`inorder`, and the recursive `tree_contains` contracted against it using the
existing function-level structural `decreases`. No dependencies.

**B3. Negative rotation regressions.**
Scope: mdtests only. A rotation that drops a subtree, one that reuses a child
twice, and one that swaps the in-order position of two nodes, each with a
contract claiming preservation, each failing at the fold or the `have` that
would state the false model. No dependencies.

### Phase C: rbtree models on the unchanged Linux shapes

Until the pinned import lands, these use mdtests whose C is the verbatim
function body from the pinned revision with its headers, in the style of
`mdtests/rb_parent_family.md`. Verbatim copies are the only acceptable
stand-in; a function edited to suit the verifier is not evidence.

**C1. `rb_at(p, parent)` and the link helpers (D1, D2).**
Scope: the rbtree model and resource; contracts for `rb_link_node`,
`rb_set_parent`, `rb_set_parent_color`, `rb_set_black`, `__rb_change_child`,
and `rb_red_parent`, each stating its effect on the model or on the frame
that owns the written cell. Regressions: positive per helper, negatives for
a wrong color bit and a parent word pointing at the wrong node. Depends on
A1 and A5; the `__rb_change_child` case at the root depends on B1's frame
shape.

**C2. Red-black pure library (D10).**
Scope: `Color`, `black_height`, `is_rb`, `almost_rb_insert`,
`almost_rb_erase`, and theorems: both rotations preserve `inorder`; recolor
preserves `inorder`; the insert fixup step on each case restores or
propagates the almost-invariant; removing a node with at most one child, and
splicing the in-order successor into a two-child node, yield
`list_remove_first(inorder(t), node)`. All pure; no C. No dependencies.

**C3. `rb_insert_color` and `__rb_insert` (D3, D4).**
Scope: the fixup loop contracted over `ctx_at(node, root)` and
`rb_at(node, parent)` with entry model almost-red-black at `node` and exit
model red-black with `inorder(plug(...))` unchanged; `decreases ctx;`.
Regressions: the verbatim function; a negative that skips a recolor. Depends
on A4, A8, A9, A10, A11, A14, A15, A16, B1, C1, C2.

**C4. Traversal and replacement.**
Scope: `rb_first`, `rb_last`, `rb_next`, `rb_prev`, `rb_replace_node`, with
results stated as first, last, successor, predecessor in `inorder`, and
replacement as the identity substitution in the model. Depends on A6, B1,
C1.

**C5. Erase (D3, D4, D10).**
Scope: `__rb_erase_augmented` and `____rb_erase_color`, contracted so the
exit `inorder` is the entry list with the designated node removed and the
exit model red-black; the two-child case uses the splice lemma. Depends on
C3.

**C6. Augmented variants and callbacks.**
Scope: `__rb_insert_augmented`, `rb_erase_augmented`, and the
`rb_augment_callbacks` contracts (`propagate`, `copy`, `rotate`) as named
contracts preserving the model, extending
`mdtests/augment_rotate_model_callback.md` and `mdtests/rb_augment_*`.
Depends on C3 and C5 and on the callback packaging in
[memory-vs-resources.md](memory-vs-resources.md).

### Phase D: pinned source

**D1. Attach the Phase C sidecars to the imported pinned translation unit**
once [kernel-scale-preprocessing.md](kernel-scale-preprocessing.md) and
[linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md) land, and
replace the verbatim-copy mdtests with the pinned regression. Depends on
everything above and on those issues.

## Acceptance criteria

- Preserve the implemented ownership-backed resource fields and compositional
  parent/child models; no generalized witness syntax is required by itself.
- Models retain pointer identity without turning pointers into arithmetic
  integers or granting pointee ownership.
- Function contracts can relate entry and exit models across a changed root.
- Loops carry named modeled instances (D5) and structural measures (D6);
  matched instances expose their selected arm at contract lowering and loop
  heads (D7); matched arms own children of other declared resources (D8).
- Reasoning and certificates are output-sensitive in the explicitly exposed
  model terms; no tactic unfolds an unknown whole tree automatically.
- Required rbtree contracts establish exact rotation order preservation,
  insertion of the designated node, erasure of the designated node, and the
  specified identity substitution on replacement. Insertion and erasure
  describe the correct sequence change, not equality with the input sequence.
- Models express parent/child consistency, acyclicity, red-black color and
  black-height invariants, and correct traversal results. Required algorithms
  establish their respective guarantees. Loop termination is coordinated with
  [structural-loop-termination.md](structural-loop-termination.md).
- Small positive and negative rotation and insert/erase regressions (synthetic
  or on the pinned source), required MVR model proofs, and
  `scripts/check.sh` pass.

Integer specification coverage is landed and documented in
[the mathematical-integer internals](../docs/internals/mathematical-integers.md);
this MVR model work has no pending dependency on the retired Integer P1
issue. Related: [algebraic-data-types.md](algebraic-data-types.md),
[resource-algebra-extensions.md](resource-algebra-extensions.md),
[memory-vs-resources.md](memory-vs-resources.md), and
[recursion.md](recursion.md).
