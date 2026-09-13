# Verify the Linux rbtree example on the recursive structure models

Renamed from `recursive-structure-models.md` on 2026-09-13 and collapsed
from its 1600-line journal to the state, the decisions, and the remaining
work. The models, the two syntax extensions (loop binders `owns name:
res(args);`, keyword-free `decreases name;`), decision D7's single
publication point, and packages A1 through A28, T1 through T8, S1, B1
through B3, C1, C1b, C2, C2b, C2c, and C4's replacement half are landed.
What remains is finishing the specific example: the verbatim `__rb_insert`
(C3), the traversals, erase (C5), the augmented callbacks (C6), and
attaching the sidecars to the pinned source (D1). The full history is in
git: `git log --follow issues/rbtree-example.md`.

P1: required for MVR. Linux rbtree does not store keys, so its generic
correctness property is preservation of node identity and in-order order
while links and colors change; a contract that consumes one well-formed
tree and produces another cannot state that without an abstract model.

## Priorities, 2026-09-13

Fix what slows the work before completing the example:

1. **Imports first.** The insert fixture is 6100 lines because a fixture
   cannot import, so the whole pure library is copied in, re-verified on
   every run, and outside audit's coverage. This issue depends on
   [specification-imports.md](specification-imports.md), whose "not an MVR
   dependency" note is withdrawn. C3 resumes only after the example can be
   written as an `examples/` project that imports `examples/rbtree-model`.
2. **Diagnostics that point the wrong way** (package T9 below), since
   several resumptions lost their budget to them.
3. **Efficiency next, if it stays on pace to be a problem.** `click verify`
   of the insert fixture went from 0.6s to 5.8s with a third of the loop
   body written, largely because the body is spelled out once per frame
   combination. Remove the duplication (a theorem per case, D10 shape),
   then measure; a verifier scaling defect is a blocker under the
   efficiency contract.
4. **Then the remaining exits of C3**, as separate packages by exit path.

## State, 2026-09-13

**The insert fixture**, `mdtests/rb_insert_color.md`: verbatim Linux
`__rb_insert` and `rb_insert_color`, C untouched. The loop carries
`owns c: ctx_at(node, root); owns t: rb_at(node); decreases c;` with nine
invariants in the frame-level form the C2c case theorems use:
`is_rb(t.model) == 1` and `ctx_almost_rb_insert(c.model,
black_height(t.model)) == 1` (the black height is the pure function of the
loop-carried model, which is how every case theorem spells its `bh`), plus
the seven link, colour, and order invariants. The contract's `requires`
were restated the same way; the restatement is a faithful strengthening
(the old `almost_rb_insert(plug(c.model, t.model))` and `ctx_root_black`
follow from it). Complete: `initialize`; the root-blackening `break`; the
black-parent `break` on both frames; `Context::Top` refuted for the
grandparent frame; the uncle's arms split. The `expect` line is the
frontier report at statement 23 (`tmp = parent->rb_right`, red uncle
skipped): "still ahead on this path: the body's end and 1 `break`. Already
complete: 2 at a `break`". Remaining: the two recolour `continue`s, the two
rotation `break`s, the body's end, the post-loop `simp()`, and
`rb_insert_color`. `click verify` takes 5.8s wall; about 0.9s is the
copied library, the rest is the body written once per frame combination.

**How the last five resumptions went.** Each stopped on one to three
verifier bugs rather than on proof difficulty, every one now closed (gaps
62 through 71 below): typing of proof-arm bindings as memory bases, inline
functions' locals with no layouts, four missed scoping sites, three
`click audit` disagreements with `click verify`, a `contradiction`
accepted only as an arm's sole tactic, and an unfinished `preserve` that
hid its frontier. Expect the same cadence on the rotation exits.

**Landed packages, one line each (commit).** A1 arm selection dff4ebdc;
A2 cross-family arm children de1da207; A3 loop binders 9e62f2a2; A4
structural `decreases` 2ab5dba3; A5 struct-pointer arm bindings as memory
bases 036170c4; A6 pointer payloads and arm scoping 7b52373a; A7 `let r =
step(...)` 9c7710ee; A8 proof `match` of any width 590b2553; A9 proof
`match` at any frontier 66bd8005; A10 wide loads named by load variable
b0cfc0e6; A11 pointer disequality from null-ness or separation ec8ffc4a;
A12 folds read their arm's cells 0e7d8000; A13 refuted arms publish
negative facts, ascent past the contract boundary 6335d1eb; A14 ascending
walks 660c7643; A15 ranked loops call inline helpers 819cb5b1; A16 `ih`
over all theorem parameters 24517c61; A17 short-circuit guard exits
1472f6f8; A18 unfold names its cells b8014f05; A19 read authority common
to possible arms eec257aa; A20 pointer-argument body facts ef856acd; A21
arm refuted from a predicate fact cbf19069; A22 ownership across a proved
pointer equality a6323676; A23 `break`/`continue` in ranked bodies
2b64528d; A24 insert contract blockers 2d84c565; A25 exits joined through
the binders ca49cf06; A26 loop bodies inside proof matches ba0d9c30; A28
one arm-publication point per frontier badc1de3; S1 unevaluable guard
conjunct refused 841126d4; T1 531b5651; T2 92a81e32; T3 bb009743; T4
63ec6190; T5 2cb5669f; T6 2ed15042; T7 b3cfc86a; T8 6426b3d4; B1 (docs
0b6016aa); B2 and B3 688e7990; C1 05257e8e; C1b node-keyed model 368c4aec;
C2 c9d5afee; C2b 427e2463; C2c 181d6db6; C4 replacement half 32992501
(traversals `rb_first`/`rb_last` and the `rb_next` guard are pinned in
`mdtests/rb_first_last.md` and `rb_next_conjunctive_guard.md`; the verbatim
`rb_next` guard `while ((parent = rb_parent(node)) && ...)` is an
assignment expression C0 does not parse, owned by
kernel-scale-preprocessing). Uniform scoping: bb142e1c (theorem arguments,
`instantiate`, `extract`), ad5c2307 (loop clauses), 2d96d5d7 (phase
bodies), 99a07d5c (`using` premises in a `have` body).

**Machine notes.** One full gate at a time; under heavy load a few unit
tests hit nextest's 60s kill with zero assertion failures and pass alone.
`scripts/check.sh` prints no marker of its own; judge it by exit status. A
fresh worktree's cold build is about 90s and 3 GB; build caches grow with
incremental work, so remove worktrees when their task lands.

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


## Closed gaps

Every gap found during the campaign, one line each, with the package or
commit that closed it. Reproductions live in the named fixtures.

| Gap | What | Closed by |
|---|---|---|
| 1 | A loop could not hold a modeled instance | A3 |
| 2 | Model-gated composite exposed no cells at contract lowering or loop heads | A1 |
| 3 | A matched arm could own only its own resource's children | A2 |
| 4 | `decreases` accepted only integers | A4 |
| 5 | Struct-pointer constructor binding not a memory base | A5 |
| 6 | Pointer payload not relatable to a C pointer | A6 |
| 7 | Structural termination ignored matched bodies | A4 |
| 8 | Pure function could not return a pointer | A6 |
| 9 | Call result in a condition had no name | A7 |
| 10 | `if` expression could not produce an algebraic value | A6 |
| 11 | Audit disagreed with verify on the scaffold | T1 |
| 12 | Proof `match` capped at two constructors | A8 |
| 13 | Loop body could not unfold its binder | A9 |
| 14 | Audit failed on other examples | T3 |
| 15 | Wide proof matches superlinear | T4 |
| 16 | Fold inside an arm lost unwritten-cell facts | A10 |
| 17 | Remaining audit disagreements | T5, T6 |
| 18 | Pointer disequality not decided from null-ness or separation | A11 |
| 19, 20, 24 | D3 frame fold and pointer-payload ownership, one bug | A12 |
| 21, 25 | Struct-pointer local had no struct layout | A12 |
| 22 | Separation from separate unfolds did not reach a later frontier | A17 |
| 23, 28 | Stale; `_Bool`/float loads unnamed | T6 |
| 26 | Selected-arm facts at contract lowering broke nine fixtures | A13 |
| 27 | Refuted arm not published as a negative fact | A13 |
| 29 | Ascending walk stopped at the contract boundary | A13, A14 |
| 31 | Soundness: unevaluable guard conjunct dropped | S1 |
| 32 | Induction hypothesis fixed every non-inducted parameter | A16 |
| 33 | Ranked loop could not call a contract-less inline helper | A15 |
| 35 | Parent-as-parameter unspellable; model re-keyed by node | C1b |
| 36 | Two evaluable guard conjuncts refused | A17 |
| 37, 38 | Load identity across an unfold | A18 |
| 39 | Guard prefix did not publish common read authority | A19 |
| 41 | Soundness: capture in pure-function unfold | C1b |
| 42, 43 | Pointer-argument body facts; payload-to-local identity | A20 |
| 44 | Two `RbTree` shapes | C2b |
| 46, 50 | `rb_replace_node_with_children` 17s; repeated work | T7 |
| 48 | Arm not refuted from a predicate invariant | A21 |
| 51 | Owned cells did not follow a proved pointer equality | A22 |
| 53 | Insert fixup parse and contract blockers | C3 (cffe7116), A23, A24, C2c |
| 54 | `break` exits had to reach one state | A25 |
| 55 | Omitted-phase planner and expansion defects | T8 |
| 56, 57 | Proof `match` around a ranked loop; `branch` in `preserve` | A26 |
| 59 | Soundness: `do ... while` exported no guard-false exit | A25 |
| 61 (a) | Contract-lowering refutation from an arithmetic requirement | A28 |
| 62 | Phase bodies did not see a proof `match` arm's bindings | 2d96d5d7 |
| 63 | Unfinished `preserve` hid its frontier | 6e81426b |
| 64 | `old(t.model)` after a pre-loop unfold hit `Paths` | 3893e6b5 |
| 65, 66 | Smart `have`s and helpers inside `initialize by { }` did not expand | 54d0f136 |
| 67 | Load through a proof-arm binding with a pure call: arm bindings were untyped in proof arms | 9a49463d |
| 68 | `simp() using` premise in a `have` body could not name an arm binding | 99a07d5c |
| 69 | Consumed instance's arm equation cited by a spelling that no longer lowered | 44acfb0c |
| 70 | `static inline` locals had no layouts (map keyed by the `#inline:` name) | ca8b75f8 |
| 71 | `contradiction` in a `preserve` arm only as its sole tactic | ccf9a340 |

## Open findings, not scheduled

Small items found along the way and recorded in the fixtures named. None
blocks C3; each is a candidate package when it starts to.

- **Diagnostics** (package T9): an empty proof `match` arm inside
  `preserve` falls through to phase automation and reports `missing
  resource fact views ...` rather than a frontier; a lowering that filters
  every path as a runtime error reports "the kernel lowering produced 0
  paths, not one" without the error (gap 67 and 70 were both a 4-byte
  read of an 8-byte cell hidden behind that message and behind
  `rewrite`'s "equality does not occur in the current goal");
  `resource_clause_position` names clause 1 when clause 2 failed; `ensures
  sub.model != Empty` on a produced instance reports "could not apply
  checked contract resource effect" instead of an unproved claim; "fold
  requires the instance body facts for the proposed fields" does not name
  the failing clause; `have (x & 1) != 0` derivable by smart reasoning
  reports "no explicit simple certificate for 64-bit equality is false".
- **Pure-proof limits:** `normalize()` and `normalize() using` do not
  close pointer-equality transitivity or symmetry inside a pure theorem
  (`simp()` does; `rewrite(a == b); normalize();` substitutes a pointer
  equality into a constructor argument while `normalize() using` does
  not); a raw `if parent == p` as a pure function's outermost test unfolds
  to one opaque bitvector operation, so predicate tests are written `if
  <int32 test> == 1`; `extract` directly inside a `match` arm is
  unsupported (gap 52).
- **Loop exits:** algebraic model values are not renamed at the exit
  join, so an exit whose binder model is the head's symbolic model leaves
  an unspellable name in its disjunct; `simp` cannot eliminate an exported
  exit disjunction or substitute an exported loop equation (`cases(...)`
  works); two ascent loops in one function fail the second loop's
  `close_invariants` with plain guards; `click expand` of a `loop` whose
  `preserve` has `match`, `unfold`, and a proof `if` with `initialize`
  omitted emits a script failing with "resource match requires constructor
  evidence" (gap 60, T5/T8 class, an audit disagreement worth a T package
  when a fixture hits it).
- **Folds and unfolds:** a body that reassigns a parameter cannot refold
  its borrowed instance at the entry position (`fold(tree_at(old(root)),
  ...)`; arguments are current-state only); an unfold of an unmatched
  composite leaves its cells unnamed; a `have color_bit(Color::Red) == 0`
  before a refold breaks the fold's exact body-fact check; a cell reached
  neither by contract materialization nor by an unfold loses its load
  identity across a write whose separation is only a resource fact.
- **Proof shapes:** the grouped driver declines a top-level `match
  c.model` after a loop while the same shape on the subtree binder works;
  a proof `if` whose arms contain a proof `match` at the top level of a
  function proof is declined by the grouped driver.
- **Not uniform:** while a contract section's clauses are evaluated one at
  a time only read authority is published, not a full arm re-decision,
  because a per-clause re-decision broke the near-linear width contract
  (A28).
- **Stale prose:** `mdtests/rb_replace_node.md` says a victim with
  children cannot be contracted, which `rb_replace_node_with_children.md`
  contradicts.

## Remaining work packages

Each lands as one coherent green commit with its regressions and docs,
judged by `scripts/check.sh`'s exit status. C is fixed; adaptation goes
into contracts, lemmas, resources, tactics, lowering, or the kernel. No
package creates issues. A package that hits a tooling failure listed in
`AGENTS.md` stops and reports.

**I1. Imports, first slice** (in
[specification-imports.md](specification-imports.md)). One-level
`import "path.click";` of pure declarations from a local file, loaded once;
the importing sidecar alone selects `verifying` sources. Then convert the
insert fixture into `examples/rbtree-insert` importing
`examples/rbtree-model`, keeping `mdtests/rb_insert_color.md` only as a
pointer or deleting it. Depends on nothing; C3a through C3c depend on it.

**T9. Diagnostics that point the wrong way.** The first list under "Open
findings". Each item gets a minimal negative fixture pinning the new
message. Depends on nothing.

**E1. Per-frame duplication and verify time.** Restate the fixup body's
per-frame proofs as one theorem per case (D10 shape) so each path is
written once; measure `click verify` before and after; if the remaining
time is superlinear in the body, reduce it to a scaling regression under
`docs/internals/verification-efficiency.md` and fix the verifier before
C3b. Depends on I1.

**C3a. Recolour `continue`s.** Case 1 on both frames: recolour parent,
uncle, and grandparent through `rb_set_parent_color`, refold at the
recoloured models, `ctx_insert_case1_left`/`_right` for the restated
invariant at the grandparent, `node = gparent; parent = rb_red_parent(node);
continue;` owing all nine invariants and `decreases c` (the next frame is
`up.up`, a strict contained descendant). Depends on I1, E1.

**C3b. Rotation `break`s.** Cases 2 and 3 on both frames: the writes
through `__rb_rotate_set_parents` and `__rb_change_child`, refolds at the
rotated models, `ctx_insert_case2_*` and `_case3_*`, then `break` owing the
binders. Depends on C3a.

**C3c. Post-loop and `rb_insert_color`.** The body's end, the post-loop
`is_rb_root(plug(ctx.model, sub.model)) == 1`, in-order preservation and
parent consistency from the joined exits, and `rb_insert_color`'s own
proof by `execute(); simp();`. `expect pass`, audit-clean; a negative that
skips a recolour. Depends on C3b.

**C5. Erase (D3, D4, D10).** `__rb_erase_augmented` and
`____rb_erase_color`, contracted so the in-order sequence loses exactly
the designated node and the exit model is red-black; the two-child case
uses the splice lemma. Larger than insert; expect the same cadence of
verifier gaps. Depends on C3c.

**C6. Augmented variants and callbacks.** `__rb_insert_augmented`,
`rb_erase_augmented`, and the propagate/copy/rotate callbacks over an
abstract augmentation. Depends on C3c and C5 and on the callback packaging
in [memory-vs-resources.md](memory-vs-resources.md).

**C4b. Traversals.** `rb_first`, `rb_last`, `rb_next`, `rb_prev` on the
verbatim bodies. Blocked on the assignment-expression guard in
[kernel-scale-preprocessing.md](kernel-scale-preprocessing.md).

**D1. Attach the Phase C sidecars to the imported pinned translation
unit** and replace the verbatim-copy fixtures with the pinned regression.
Depends on C3c, C5, C6, C4b, and
[kernel-scale-preprocessing.md](kernel-scale-preprocessing.md).

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

