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
on A4, A8, A9, B1, C1, C2.

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
