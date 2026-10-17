# Verify the Linux rbtree example on the recursive structure models

Priority: P1.

Soundness: not soundness. This is example delivery. The soundness defects
found along the way are fixed and listed in the package table (rows 31, 41
and 59).

Renamed from `recursive-structure-models.md` on 2026-09-13 and collapsed
from its 1600-line journal to the state, the decisions, and the remaining
work. The models, the two syntax extensions (loop binders `owns name:
res(args);`, keyword-free `decreases name;`), decision D7's single
publication point, and packages A1 through A28, T1 through T8, S1, B1
through B3, C1, C1b, C2, C2b, C2c, and C4's replacement half are landed.
What remains is finishing the specific example: the verbatim `__rb_insert`,
the traversals, erase, the augmented callbacks, and attaching the sidecars
to the pinned source. That work is numbered as
[chunks 1 to 24](#remaining-work-chunks-1-to-24), one pull request each. The
full history is in git: `git log --follow issues/rbtree-example.md`.

P1: required for MVR. Linux rbtree does not store keys, so its generic
correctness property is preservation of node identity and in-order order
while links and colors change; a contract that consumes one well-formed
tree and produces another cannot state that without an abstract model.

## State, 2026-10-09: handoff

Insert is finished. The black-successor splice's deficit-start model proof
in [chunk 10](#erase-d3-d4-d10) covers immediate and deep successors.
Chunk 11 now verifies the unchanged C for zero/one-child deletion and every
immediate-successor exit, at the root or below it on either parent link.
Red-leaf and nonempty-child successors return balanced trees with null fixup;
black-leaf successors retain the exact deficit context and return the successor
for fixup. Exact models preserve parent consistency and in-order contents.
Deletion at any tree position with a deeper red-leaf successor or a nonempty
replacement child verifies in `rbtree_erase_spine.click`. The C descent loop carries the exact
left-only `EraseSpine`; opening and closing helper contracts expose its
innermost link around one shared C continuation. `refold_erase_spine` rebuilds
the path, and `rb_erase_no_fixup_successor_splice` proves balance, exact
in-order removal, and parent consistency for both complete transplants.
The verified parent-link call preserves the outer context. The leaf and
nonempty-child C branches join before shared spine and outer-context
reconstruction. The contract returns the exact whole-root model, detached-node
ownership, and null fixup.
Deletion at any tree position with a deeper black-leaf successor verifies in
`rbtree_erase_black_spine.click`: the terminating graft helper joins the
retained descent spine to the transplanted successor's context. Its contract
returns the empty deficit hole, exact context, red-black and parent-consistency
invariants, in-order contents, detached-node ownership, and the nonnull minimum
parent for color repair. Both deeper sidecars share the spine model and resource
modules. The generalized black-leaf proof preserves the outer context through
one verified parent-link call and reconstructs the exact deficit at any tree
position. All 136 expansion-audit sites pass across the shared model and
black-leaf sidecar; its four splice/fixup mutations are rejected, and the
red-leaf/nonempty-child sidecar now also covers arbitrary outer contexts.
Deeper-successor mutation checks run nightly. All unlink-function exits are
covered across the sidecars, completing chunk 11. Erase-color repair now covers
repeated propagation followed by all black-sibling cases and red-sibling cases
1/2 and 1/4 in either direction. Red-sibling cases 1/3/4 after propagation remain.
The C parent-link helper now verifies separately in `rbtree_change_child.click`
for root, left, and right links. Its contract transfers the surrounding context
to the new focus with the same model and preserves the old node's tag; three
mutation checks reject missing link updates in about two seconds each, and all
ten helper expansion-audit sites pass. Deeper non-root proofs can use
this verified call instead of duplicating the parent-link cases.
The next proof exposed a missing 64-bit equality case in explicit pointer-offset
rewriting. Field facts now rewrite through a loaded pointer alias at both
32- and 64-bit widths; positive and false-conclusion fixtures cover the fix.
The non-root continuation also exposed missing 64-bit cached-read normalization
after a store followed by a named-resource call. Signed and unsigned wide reads
now reuse their exact cached value, preserving read kind and recorded history;
explicit `normalize` establishes the framed equality. Regressions reject changed
and partially overwritten values and check scaling with unrelated cached cells.
Pointer-valued fields copied between independently returned nodes now also
retain their full value across a framed call. The checked memory walk recovers
the stored pointer, including its block, instead of comparing only read offsets.
The reduced caller and an overwrite negative exercise this non-root splice path.
Explicit field propositions now also retain the imported ABI slot width.
Previously `separate(memory(node->tag), ...)` treated an eight-byte tag as
four bytes, so the frame proof could not clear the helper's complete write.
A reduced modeled-child caller verifies with the corrected separation; an
overwrite negative and field-viewability checks cover the boundary.
Caller-kept ranges now also follow exact aliases of a field's base, including
aliases introduced by unfolding a modeled node. Typed evidence checks the whole
access before allowing a framed read. Tests reject overwritten fields, partial
coverage, and withdrawn aliases, and bound lookup work with unrelated ownership.

Opening a parent with named children now retains its direct pointer aliases
before naming the immediate fields and child arguments. Surface materialization
uses that same checked naming context, while pure body facts keep their model
bindings. Reduced refolds after unrelated stores and a call pass; stale-pointer
and unproved-fold-alias variants are rejected. Existing exact scalar and
nonnull body-fact proofs retain their original spellings.
Explicit `transport` now shares its existing context-keyed failure memo across
its proof routes. The frozen non-root pointer frame returns a local refusal
instead of exhausting the simple budget. A reduced frame refusal is pinned
below 250,000 units, with a separate check that grows unrelated premises. The
non-root splice proof uses explicit frame and packed-parent facts.
The packed-parent reduction exposed a certificate gap when reading low tag
bits back from an aligned pointer word. Explicit arithmetic now checks that
projection using only the selected alignment and word syntax, including
masked tags and unsigned addition. Negative checks reject insufficient or
foreign alignment and changed tag bits; deterministic work checks cover
growing words within the certificate's existing payload bound.
A smaller named-call reduction also exposed a missing explicit read-value
normalization route. `normalize() using { child == identity; }` can follow
the typed memory history to a wide stored value using the cited alias and
the call’s recorded caller-owned ranges. The original `normalize()` remains
context-free; partial overwrites and withdrawn aliases do not recover a value.
The structural frame comparator also now includes 64-bit equality. Its missing
case blocked the parent-word frame across the successor’s final tag write. A
quantified wide-array equality reproduces the refusal on the prior checker and
passes with the same checked load-history rule used for 32-bit equality. The
black-leaf sidecar now verifies through its final augmentation callback for
root, left-child, and right-child transplants, retaining the original outer
context. The callback resource stays folded across the parent-link helper call.
The generalized red-leaf/nonempty-child continuation exposed a join-lowering
bug: a comparison mentioning a mark was treated as wholly historical even
when its other side read current memory. Every exported interface fact now
gets checked state-parametric lowering with the snapshots shared by both
arms; the marked expression stays fixed while the current read is checked at
each frontier. A loaded-pointer reduction pins the former kernel refusal.
The generalized proof also exposed lost source names in exported interface
facts: later snapshot rewrites printed resolved model pointers as `…`. Interface
checking now retains the written facts alongside resolved values. A reduced
packed-word rewrite and the complete successor expansion audit cover the fix.
The reduction also exposed lost element types for loaded local pointers in
branch interfaces. Interface lowering now looks up each referenced declaration
in the current state while keeping values symbolic; a small wide-word fixture
checks that both arm proofs agree with the kernel join.
The first erase-color proof also exposed a discarded theorem-premise refusal
inside model-match arms. Written arm applications now retain that diagnostic
instead of blaming an unsupported proof shape; a reduced negative pins it.
The color-flip proof also exposed discarded alias facts in named-fold
arguments. Folding now evaluates those arguments with the checked facts at the
current frontier, as branch interfaces already do. A reduced model-pointer
field read verifies and expands; an unproved model alias remains unreadable.
The loop-exit bug exposed by the C application is fixed: guard-false, break,
and return exits retain the final resource binders and restore the withheld
caller frame. Small regressions also cover stores through reconstructed node
pointers without losing unrelated caller-owned fields.
The deeper splice also exposed pointer-identity losses at checked reads,
same-block alias transitivity, and seeded pointer fields at nonzero offsets.
These now have focused regressions in `stored_pointer_child_survives_resource_unfold.md`,
`pure_pointer_transitivity_same_block.md`, and
`model_pointer_alias_nonzero_field_load.md`. Entry-time `if` and `match`
interfaces now bind the checked function arguments before joining, so a
proof-only ownership split can rejoin and then start C execution. Post-loop
interfaces also retain pointer-read congruence: checked equality premises
register their read definitions, and interface pointer equalities normalize
against that scoped graph (`proof_interface_pointer_read_congruence_after_loop.md`).
Unfolded scalar cells also retain the pointer spelling used by their checked
body facts when the unfold itself introduces a new alias. Indexed reads reuse
that cell through the C parameter without granting read authority or carrying
facts across a write (`unfold_child_preserves_scalar_cell_identity.md`).
Matching a rebuilt model now also preserves an existing algebraic payload's
identity under its new source name. The red-leaf extension exposed this at the
successor's color check; `proof_match_preserves_algebraic_payload_identity.md`
and its overwrite negative cover it, alongside indexed constructor checks.
The deeper black-leaf prototype also exposed missing null-pointer argument
typing in user tactics. A literal `0` now receives the declared pointer type,
as it does at resource and pure-function parameters; nonzero integers and
integer variables remain rejected.
Tracing the black-leaf prototype exposed repeated project resolution for
each written tactic location. The CLI now resolves a claim's locations
together and reuses them, with deterministic scaling checks. The original
trace finishes in about 15 seconds instead of hitting its 60-second bound.
The black-leaf context folds also exposed an alias gap for C pointers with a
symbolic base and scaled offset. Fold-body checks now query exact aliases of
the pointers in the requested fact, including pure-function arguments, and
require exact evidence for the rewritten fact. Kernel regressions cover
nonnull and parent-function facts, missing evidence, false conclusions, and
16/64/256 unrelated aliases including null links.
Documenting the shared spine modules exposed a parser/documentation mismatch:
Click now accepts the documented `//` and `/* ... */` comments in both parsing
and source-location scanning. Regressions cover imported modules, expansion
offsets, literal contents, division, and unterminated block comments; the
existing `#` spelling remains supported.
The first C-port attempt exposed an imported-resource binder collision, now
covered by a regression and fixed by scoping learned binders to each declaration.
The insertion resources are shared in `examples/rbtree-model/rbtree_resources.click`.
The loaded tagged-null conversion bug found in the root-leaf case is also
fixed: explicit 64-bit casts now accept values proven zero by the current
facts. `mdtests/tagged_pointer_null_word.md` covers loaded zero and masked
loaded tag words, with a separate nonzero-load rejection fixture.

`examples/rbtree-erase/rbtree_erase.click` consumes the focused `rb_at(node)`
and its `Context::Top` resource and returns the detached node's raw fields and
a whole root resource. It handles leaf, right-child, and left-child root
removal, proves null as the fixup parent, and establishes a black-rooted
red-black result with in-order sequence `left ++ right`. The imported
`rbtree_erase_root.click` proves those model facts separately. Mutation tests
reject missing root replacement and either missing child parent/color write.
`rbtree_erase_successor.click` adds the immediate red-leaf successor case at
the root (2026-10-08). It proves the exact successor-splice model, red-black
validity, parent consistency, in-order contents, detached-node ownership,
and null fixup parent. All five smart sites pass expansion audit. Mutations
remove the successor's parent/color assignment or its new left child's parent
assignment and are rejected.

The post-return fold bug is fixed: checked `have` completions are retained on
the returned path, bound to its program snapshot, with root assumptions
checked once and subsequent persistent deltas checked incrementally. Kernel
regressions reject sibling facts and different memory snapshots and check
scaling; mdtests cover interleaved proofs and folds. Exact fact lookup now
recognizes retained resource-composition facts. Explicit resource closers use
the same checked ownership receipts as `simp`, fixing the successor's final
expansion without changing C.

`rbtree_erase_black_successor.click` covers the immediate black-leaf successor
at the root (2026-10-08). Its output is the empty hole and exact deficit
context, with `ctx_rb(..., Succ(Zero), Black)`, parent consistency, and
remaining in-order contents. The returned fixup parent is the non-null
successor. All five smart sites pass expansion audit. Mutations reject
returning null or skipping root replacement.
The proof also exposed scalar pure-function calls skipped by pointer
`rewrite`; the existing binder-safe pointer walker now handles those goals,
with missing-premise, capture, offset, snapshot, and scaling regressions.

`rbtree_erase_child_successor.click` covers the immediate successor with a
nonempty right child at the root (2026-10-08). Its `rb_immediate_successor_child`
model reattaches the old left subtree and blackens the replacement child.
`rb_erase_immediate_successor_child` proves balance under a valid outer context,
local parent consistency, and the exact in-order sequence. The C contract
returns that model, full root validity and parent consistency, and a null
fixup parent. Neither the successor's nor its child's color is assumed by the
contract. Mutation checks cover the required blackening write.

`rbtree_erase_black_leaf.click` verifies non-root black-leaf deletion on both
parent links. It returns the unchanged context model, an empty hole with a
one-black-level deficit, parent consistency, and the non-null fixup parent.
It holds and returns exclusive callback-table ownership. Mutation tests reject
an unchanged left or right parent link and a null fixup return.
`rbtree_erase_red_leaf.click` covers both parent links without a deficit: the
empty hole fits the unchanged context at the same black height, and the return
is null. Its mutations reject unchanged links and a non-null fixup return.

`rbtree_erase_right_child.click` and `rbtree_erase_left_child.click` cover
one-child deletion at the root and on both non-root parent links. They derive
colors from red-black validity, return the exact blackened/reparented
replacement and
unchanged context, and prove whole-tree balance, parent consistency, in-order
contents, and null fixup. `rbtree_erase_one_child.click` supplies the balance,
local symmetry, and parent-consistency theorems. Mutation tests reject unchanged
parent links, skipped parent/color writes, a red replacement, and non-null fixup.

`rbtree_erase_nonroot_successor.click` extends immediate red-leaf successor
splicing to both non-root parent links. It preserves the outer context and
returns the exact replacement subtree, whole-tree balance, parent consistency,
and in-order contents with null fixup. The erased node's color is not assumed.
Six mutation tests cover both parent links, left-subtree attachment and parent
updates, the successor's parent/color write, and the no-fixup return.

`rbtree_erase_nonroot_black_successor.click` covers immediate black-leaf
successors on both parent links. Its exact deficit context preserves parent
consistency and completes to the intended splice in the original outer context.
The returned fixup parent is the successor. Seven mutations cover the link and
parent/color writes, null return, and returning the erased node's parent.

`rbtree_erase_nonroot_child_successor.click` covers an immediate successor
with a nonempty replacement child on either parent link. Its exact model
blackens the child while preserving the outer context. Whole-tree balance,
parent consistency, in-order contents, and null fixup follow without color
assumptions. Eight mutations cover all required link and parent/color writes,
child blackening, and the no-fixup return.

The broader example gate exposed two post-return certification regressions in
`arena_write` and `arena_region_length`. Exact-width readability of a
materialized cell and immutable argument facts of ordinary held resources
are now retained. Argument facts are instantiated without memory, resources,
or ambient read premises; mutable invariants and authorized member bodies
remain unavailable through this route. Focused regressions cover range and
lifetime rejection, resource presence/quantity, and scaling.

Two proof-driver fixes support this increment: named folds after return inside
`open` are deferred to the returned state, and exact checked execution retains
its loop semantics even when no loop was reached. Thus the unreachable
successor loop does not demand a spurious ranking measure; reachable unranked
loop summaries still fail termination checks. The replacement-child checks
also exposed a theorem planner bug: it omitted a proved constructor inequality
from `apply using` even though the simple checker needed it. The planner now
retains that evidence, with positive, negative, and expansion regressions.

This section records what changed in the verifier since the insert proof was
first written, and how to write the erase proofs so they do not need the same
rework.

**Where insert stands.** `examples/rbtree-insert/rbtree_insert.click` is about
2,500 proof lines for 136 lines of C (19 times) and verifies in about 5.4
seconds at 0.43 GB peak. The size and speed targets are in
[verification efficiency](../docs/internals/verification-efficiency.md#proof-size-and-speed-targets).
What repetition remains is the left/right mirror, which needs a language
feature, and the uncontracted `__rb_rotate_set_parents` helper, which would
need a ghost argument.

**A split must rejoin.** The verifier no longer checks what follows a proof
`if` or `match` once per arm. Two arms that both continue must join, or the
proof is refused (`mdtests/proof_if_arms_must_rejoin.md`); the same holds
inside `preserve`, and the automatic loop closer joins a C `if` that has more
body after it instead of walking every path. The rule and its exceptions are
in [proof scripts](../docs/concepts/proof-scripts.md) and
[loops and invariants](../docs/concepts/loops-and-invariants.md). The insert
proof was reworked to this after the fact; that rework, with hoisting and the
removal of unneeded steps, took it from about 35 times its C to 19. Write
erase this way from the start:

- Use `match ... ensuring { ... }` (or `if ... ensuring`) and state in the
  interface what the rest of the proof needs: the resources by name and the
  facts about their models. Anything an arm establishes and the interface
  does not state is gone after the join.
- A bare `branch`, or a split with no `ensuring`, joins arms that end apart
  and keeps only what both arms hold alike
  (`mdtests/a_bare_branch_joins_arms_that_end_apart.md`).
- Statements every arm repeats belong before or after the split, not in each
  arm.

**Idioms the insert port settled.**

- Fold with the matched name as the model, `fold(rb_at(0), { model: xsib })`
  rather than `{ model: RbTree::Empty }`. The fold then gives
  `xs.model == xsib` exactly, which is the interface fact, with no extra
  `have` in each arm.
- An interface fact holds in an arm only together with what its terms need to
  denote a value. `fact p[j] <= p[j + 1]` needs `have defined(j + 1)` in each
  arm (`mdtests/an_interface_fact_needs_its_terms_defined_in_each_arm.md`,
  `mdtests/bubble_pass3_max_suffix.md`). The refusal names what is missing.
- An interface may name a resource through a pointer the model binds, as in
  `owns xs: rb_at(xid->rb_left)`, when the proof holds the equality that says
  which object `xid` is
  (`mdtests/an_interface_resource_argument_reads_through_a_model_pointer.md`).
  The four `match xsib ensuring` joins in the insert proof use it: each arm
  folds only the sibling, and the context is folded once after the join.
- About a quarter of the `have` steps in the first insert proof were not
  needed. Before delivering a chunk, delete each `have` in turn and keep the
  deletion when the proof still verifies.

**A known cost, not yet measured on erase.** A store through a pointer asks,
for every remembered cell under any pointer not proven distinct from the
written one, whether ownership keeps that cell
(`CMemory::without_possible_aliasing_cells`). Each question is cheap, but
there is one for each such cell, so a `step()` that stores costs more as more
nodes are unfolded. It was left alone on insert because its share of the 5.4
seconds was never measured. Erase holds more nodes unfolded at once. If
verify time grows faster than the proof does, this is the first suspect: it
is a tooling blocker under `AGENTS.md`, to be reduced to a scaling test over
several node counts and fixed in the kernel (ask once for each owned member
instead of once for each cell), not worked around in the proof or the C.

**Running things.**

- Run heavy jobs one at a time under a memory cap, for example
  `systemd-run --user --scope -q -p MemoryMax=14G -p MemorySwapMax=0 <cmd>`.
  An uncapped `click audit` of this example once exhausted a 31 GB machine.
  `click audit` of `__rb_insert` expands once for each site and was about 33
  seconds a site when last measured on 2026-10-06, before the proof shrank;
  measure it again before relying on it. `click verify` is the routine
  check.
- Running a test binary by hand needs `RUST_MIN_STACK=8388608`, which
  `scripts/check.sh` sets; without it some tests overflow the stack.
- On a machine without the current C++ exporter, eight mdtests (`cpp_*` and
  `field_borrow_parent_drop*`) and `examples/basic-cpp` fail with
  "unsupported C++ exporter schema". They are unrelated to this work.

## State, 2026-10-02

**`__rb_insert` verifies end to end** on the unchanged Linux C
(`examples/rbtree-insert/rbtree_insert.click`, in the example gate), and since
2026-10-03 with the root-form contract: it produces the whole fixed-up tree at
`root->rb_node` as `rb_root_at(root)`. The recursive user-defined tactic
`refold_to_root` folds the context frames above the fixup's stopping point back
into one tree in a single application. **`rb_insert_color` verifies too**:
inline helpers with a verified contract are called through it, so its one call
to `__rb_insert` applies that contract.

## Priorities, 2026-09-13

Fix what slows the work before completing the example:

1. **Imports first: delivered.** `examples/rbtree-insert` now imports the
   shared `examples/rbtree-model/rbtree_model.click`; its C is unchanged and
   the unfinished proof remains an explicit negative frontier. I1 was the P1
   dependency; all retained import follow-ups are P2 and block neither C3 nor
   C5. C6 depends on callback packaging, not broader imports, unless its final
   design requires a named callback contract to cross a module boundary.
2. **Diagnostics that point the wrong way** (package T9 below), since
   several resumptions lost their budget to them.
3. **Efficiency next, if it stays on pace to be a problem.** `click verify`
   of the insert fixture went from 0.6s to 5.8s with a third of the loop
   body written, largely because the body is spelled out once per frame
   combination. Remove the duplication (a theorem per case, D10 shape),
   then measure; a verifier scaling defect is a blocker under the
   efficiency contract.
4. **Then the remaining exits of C3**, as separate packages by exit path.

## State, 2026-09-26

**C3b is started on the left-left frames.** The model gains
`ctx_insert_case3_left_step` / `_right_step` (in-order, `is_rb_root`, parent
consistency, and the sibling's black root, all stated on the context the loop
hands back at the `break`) and the parent-consistency converse and swap lemmas
they rest on (`plug_parent_consistent_ctx`, `ctx_consistent_swap`). In the
frontier, the black-uncle arm of the cursor-`Left`, grandparent-`Left`
combination runs case 3 to the `break` on six of its eight leaves: the split is
the parent's other child (empty or a node, for `if (tmp)`) times the
grandparent's own frame (`Top`, `Left`, `Right`, for `__rb_change_child`, which
`step()` executes inside one inline call). The report is now at statement 42,
`augment_rotate(gparent, parent)`, with 9 `break`s and 4 `continue`s complete;
`tests/examples.rs` pins it. Verify time of the frontier went from 1.5s to 3.7s
on a warm release build for six new leaves, each about 150 lines of proof;
that is a measurement, not yet a scaling check.

Gaps 74 and 75 below were fixed on the way. The 2026-09-29 recheck on
`f01a85a1a` leaves the frontier unchanged. An immediate sibling refold under
its model identity now passes owned-cell consumption and fails instead at
`selected child does not satisfy the proposed parent model`: the left child's
pointer argument does not match, while its model field does. A small no-write
unfold/refold reduction reproduces this; refolding at the original pointer
passes. The related `p->word` / `id->word` regression already passes.
That historical reduction now passes: checked child-read definitions retain
their graph identity, and the later read-identity recheck accepts the immediate
sibling refold. See the [checked pointer-read design](../docs/internals/equality-closure.md#checked-pointer-read-sources).
The original frontier remains at statement 42; the next `step()` stops on two
successors in the inlined rotation. The completed equality migration does not
establish that those remaining rbtree leaves verify.

The remaining C3b work after that gap: the empty-uncle leaves of the same
combination (the text is the same after refolding the uncle as `Empty`), the
other three combinations (the two inner ones add case 2's rotation first; the
model has `ctx_insert_case2_*` but no `_step` form yet), then C3c.

## State, 2026-09-25

**C3a is written on all four frame combinations.** The uncle-red `continue`
of `__rb_insert` now recolours the uncle, the parent, and the grandparent,
refolds the three nodes at their recoloured models, and closes the nine
invariants and the two-frame `decreases c` descent, for the cursor's frame
`Left` or `Right` inside the grandparent's frame `Left` or `Right`. The C
proof of each arm unfolds one cursor frame with `plug_left_frame` or
`plug_right_frame` and applies one of the new model theorems
`ctx_insert_case1_left_step` / `ctx_insert_case1_right_step`, whose four
conclusions are stated on the explicit recoloured subtree; the parent
consistency half rests on the new colour-erased `Links` skeleton
(`plug_insert_fix_recolor_parent_consistent`). This is the D10 shape E1 asked
for: the case reasoning lives in the model once, and each C arm is the
bookkeeping between the frame's own facts and the theorem's spelling. The
four arms remain written out per D9. The kernel gap it exposed (73 below) is
closed in 9e1c4281.

The loop rule was certified end to end only in a scratch experiment whose C
copy cut the uncle-black paths short with a `break`; on the unchanged source
the frontier report for the first uncle-black path preempted the back-edge
check of the completed paths at the time, so the recolour arms' closers were
validated there by explicit `have`s of every invariant in the rebound binder
spellings immediately before `close_invariants()`. Since the frontier fix the
next day, the finished arms' closers are checked on the unchanged source
before that report. The frontier is now the uncle-black
case, statement 22 of the body (`tmp = parent->rb_right`), which is where C3b
starts on all four copies; `tests/examples.rs` pins that diagnostic. The
frontier verifies to that point in about 2.8s on a warm debug build.

Three tooling limits met on this resumption were fixed the next day: a lone
sidecar now selects a project root covering its imports, so
`rbtree_insert.frontier` verifies from the command line; `--trace-to` reaches
tactics inside proof `match` arms and loop phases; and a finished `preserve`
arm's back edge is checked before an unfinished sibling's frontier is
reported (`mdtests/preserve_finished_arm_checked_before_frontier.md`).

## State, 2026-09-13

**The traversal parser prerequisite:** the unchanged `rb_next` guard
`while ((parent = rb_parent(node)) && node == parent->rb_right)` now parses and
lowers through checked statements. The assignment result has the target's
scalar type, its right operand is evaluated exactly once, the second conjunct
remains short-circuited, and a loop guard reruns the assignment after every
iteration and `continue`. The retained `mdtests/rb_next_conjunctive_guard.md`
now reaches its next bounded proof frontier: `execute()` needs a view of
`node->rb_right` while the entry `rb_at(node)` remains folded. C4b still owns
the complete descent/ascent proof; this support does not claim traversal
verification.

**The insert fixture**, `examples/rbtree-insert`: `rbtree.h` and
`rb_insert_color.c` retain the verbatim Linux `__rb_insert` and
`rb_insert_color` C formerly embedded in `mdtests/rb_insert_color.md`.
`rbtree_insert.click` is a green import/load entry and does not claim the
insert proof is complete. `rbtree_insert.frontier` imports the shared model
and retains the complete contract and unfinished proof; a dedicated regression
requires its bounded failure at statement 23. The loop carries
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
`rb_insert_color`. The focused imported-frontier regression currently reaches
the expected diagnostic in about 1.3s on a warm debug build; that timing is
supporting evidence, not a new gate, and E1 still owns the per-frame proof
duplication. The fifth resumption's branch draft (the red-uncle `Top` frame,
reading `gparent->__rb_parent_color` after `gparent == cgp`) stopped on
gap 72, a kernel read-permission bug; with it fixed the draft reaches
statement 42, `augment_rotate(gparent, parent)`, in case 2.

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
assignment-expression guard now lowers, and the latter fixture records the
next folded-entry proof frontier). Uniform scoping: bb142e1c (theorem arguments,
`instantiate`, `extract`), ad5c2307 (loop clauses), 2d96d5d7 (phase
bodies), 99a07d5c (`using` premises in a `have` body).

**Where to pick this up.** C3b starts from the frontier in
`examples/rbtree-insert/rbtree_insert.frontier` at the `Color::Black` arm of
each `match uncolor`, which stands before `tmp = parent->rb_right` (or
`rb_left`) with the uncle's cells unfolded as `ul`/`ur`, the grandparent
frame unfolded as `us`/`uu`, and `cup == Context::Left(...)`/`Right(...)`
already restated in constructor form. The branch `claude/rsm-c3-insert-fixup-7`
named earlier no longer exists. To iterate on the frontier from the command
line, copy it beside a copy of `examples/rbtree-model` under one scratch
root and verify that directory (see the fixture README). Each resumption so
far was one agent per package with the orchestrator integrating; doing the
packages directly works the same way, the packages below are written to be
self-contained either way.

**Machine notes.** One full gate at a time; under heavy load a few unit
tests hit nextest's 60s kill with zero assertion failures and pass alone.
`scripts/check.sh` prints no marker of its own; judge it by exit status,
and check for a running gate with `pgrep -x -f "bash scripts/check.sh"`
(a plain `pgrep -f` matches its own wrapper shell and deadlocks a queue).
A fresh worktree's cold build is about 90s and 3 GB; build caches grow
with incremental work, so remove worktrees when their task lands. The
other agents' worktrees under `/private/tmp/click-*` held 150 GB of build
caches on 2026-09-13; deleting `target/` of any not touched that day is
safe and was what kept builds possible. sccache was measured and removed:
this crate has 26 registry dependencies worth seconds, and neither the
`click` library (cache key includes the working directory) nor the
binaries and test binaries (they link) are shareable across worktrees.
Two tooling ideas not done: `click audit` on only the `expect pass`
fixtures a commit touches, run at integration rather than in the gate
(three of the last ten bugs were verify passing while audit failed, each
found only by hand); and splitting the unit tests that take over 15s idle.

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
equations, the explicit child map on fold, `let { ... } = unfold(...)` naming, and
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
beyond D5 and D6. Superseded in part on 2026-10-03: user-defined tactics
(`docs/internals/user-defined-tactics.md`) now give recursive,
resource-transforming steps, such as `refold_to_root`. The following stay out
of scope for every package here: a binder map on loop
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
| 72 | A read through a symbolic identity proved equal to a C pointer was refused: the read lookup resolved to the alias and looked only there | a3b96c12 |
| 73 | `if (parent != tmp)` undecided with both nodes owned: the separation rule read only assumed compositions, and two instances opened one at a time never shared one; a comparison now composes its own two holders through the alias component | 9e1c4281 |
| 74 | A fold's arm fact lowered a frame identity through its proved-equal C local inside a pure-function argument, so the fact proved in the model's spelling did not count; body facts are now also matched after substituting one pointer by an exact alias | this change (frontier leaves) |
| 75 | `rewrite(p == 0)` did not reach `(uint64)p` in a 64-bit goal, and `address(null)` was opaque to `normalize` | this change, `mdtests/rewrite_pointer_null_into_an_address.md` |

## Open findings, not scheduled

Small items found along the way and recorded in the fixtures named. None
blocks C3; each is a candidate package when it starts to.

- **Diagnostics** (package T9, landed 14d6e92c): a lowering whose every
  path ends in a runtime error now names the error (a typed load that does
  not fit its cell names its width, pointer, and the value found); a
  refused `rewrite` prints the lowered equality and goal; a refused fold
  names which fact of which arm; a failed contract resource transition is
  described rather than dumped; an empty `preserve` arm is named in the
  frontier report. Not reproduced, no change: the clause-position note
  naming the wrong clause; "could not apply checked contract resource
  effect" for an unproved produced-model claim (the shapes tried report an
  unclosed goal). Closed 2026-09-14: a justified 64-bit bit-test inequality
  now expands to its selected equality rewrite and a checked context-free
  normalization; `mdtests/wide_inequality_certificate.md` retains the pure
  regression and its required set-bit premise.
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
- **Pointer spellings across a write or a fold:** a fold at an arm identity
  after a store to another owned node verifies (chunk 1). The logical form
  now verifies too: `have id->right == p->right` and marked reads through
  `id` use the admitted footprint's address spelling, for every node field.
  Writes that reach the cell remain refused through both spellings
  (`mdtests/arm_identity_read_node_write_refused_id.md` and its `_p`, alias
  siblings). Loads in fold
  arguments (`fold(rb_at(x->left), ...)`) are unsupported.
- **Stale prose:** `mdtests/rb_replace_node.md` says a victim with
  children cannot be contracted, which `rb_replace_node_with_children.md`
  contradicts.

## Remaining work: chunks 1 to 24

Renumbered on 2026-10-02, and the importer chunks again the same day once
the pinned source was measured. A **chunk** is one pull request: one coherent green
commit series with its regressions and docs. C is fixed; adaptation goes into
contracts, lemmas, resources, tactics, lowering, or the kernel. No chunk
creates issues. A chunk that hits a tooling failure listed in `AGENTS.md`
stops and reports; if the failure needs its own kernel fix, that fix is its
own pull request ahead of the chunk.

The dated state sections, decisions, and tables elsewhere in this file, and
some fixtures and other issues, still use the earlier package names. They map
as follows:

| Earlier name | Now |
| --- | --- |
| I1 (imports), E1 (per-frame duplication), C3a (recolour `continue`s) | landed |
| C3b (rotation `break`s) | chunks 1 to 6 |
| C3c (post-loop and `rb_insert_color`) | chunk 7 |
| C4b (traversals) | chunks 8 and 9 |
| C5 (erase) | chunks 10 to 13 |
| C6 (augmented variants and callbacks) | chunk 14 |
| [kernel-scale-preprocessing.md](kernel-scale-preprocessing.md), [linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md) | chunks 15 to 23 |
| D1 (attach sidecars to the pinned source; not design decision D1) | chunk 24 |

Chunks 8, 10, and 15 have no unlanded prerequisite; chunk 3 is landed.

### Insert

Case 1 (uncle red) is written on all four frame combinations and every tactic
is checked on the unchanged source; the loop rule itself is certified once
the uncle-black arms also end, which is chunk 6. Measure verify time again as
the rotation arms land: a superlinear step is a scaling regression under
`docs/internals/verification-efficiency.md`.

**Chunk 1. Last two left-left leaves: landed 2026-10-02.** The two case-3
leaves under a `Right` great-grandparent frame in the cursor-`Left`,
grandparent-`Left` combination run to the `break`: the sibling `xs` is
unfolded so that `parent->rb_left == old` in the inlined `__rb_change_child`
is decided, `step()` runs the rotation, and `xs` is refolded at its arm
identity with `fold(rb_at(yid), ...)` before the frame refolds the finished
leaves already use. The frontier report is now at statement 23,
`tmp = parent->rb_right`, with 11 `break`s and 4 `continue`s complete;
`tests/examples.rs` pins it.

Two earlier readings of this leaf were wrong. The "two statement successors"
stop reported on 2026-09-30 was not a kernel gap: it appears only when `xs`
is refolded before `step()`, which hides the cells that decide the test. The
refusal of the post-step refold (`selected child does not satisfy the proposed
parent model`) was not a missing read identity across the rotation's stores
either. The unfold's cells were still cached as a seeded run, and the load of
`yid->rb_left` missed its slot because the run lookup reached the run's base
only through an alias index keyed by the exact pointer, so `id` found the run
at `p` and `id + 8` did not. The lookup now asks the equality graph for the
load's address in the run's block
(`mdtests/fold_at_arm_identity_after_store_to_other_node.md` and three
negatives; see
[the equality-closure note](../docs/internals/equality-closure.md#checked-pointer-read-sources)).

**Chunk 2. Empty-uncle leaves of left-left: landed 2026-10-02.** All eight
leaves under an empty uncle run case 3 to the `break`. The uncle is refolded
as `fold(rb_at(tmp), { model: RbTree::Empty })` with
`rb_root_black(RbTree::Empty) == 1` by unfolding, and the rest is the
node-uncle arm's text with the uncle model spelled `RbTree::Empty`; the arm
starts one statement earlier than the old three-`step()` stub left it, at the
join after `if (tmp && rb_is_red(tmp))`. The frontier report named this path
before the change (checked by advancing each empty-uncle leaf one step: only
this one moved the report, although the report's `tactic@` line points at the
last leaf in the file). It is now at statement 52, `tmp = parent->rb_left`,
with 19 `break`s and 4 `continue`s complete; `tests/examples.rs` pins it.
Verify time of the frontier on a release build, user seconds, load average
about 10: 3.1 with 9 `break`s, 3.2 with 11, 4.3 with 19.

**Chunk 3. Case-2 step theorems — landed 2026-10-02.**
`ctx_insert_case2_left_step` / `_right_step` state the model between the
case-2 rotation and the case-3 code, with conclusions in the spelling
`ctx_insert_case3_*_step` takes with parent and cursor exchanged.
`ctx_insert_case2_left_exit_step` / `_right_exit_step` chain the two and
conclude on `plug(up2, rotated subtree)`, because `node` is the subtree root
at this `break`. The exit spelling was inferred from the C and the finished
left-left leaf; chunk 5 is its first consumer.

**Chunk 4. Right-right combination: landed 2026-10-02.** The mirror of
left-left, case 3 only: sixteen leaves, eight under a black node uncle and
eight under an empty one. The text is the left-left arms' with the cursor,
grandparent, and uncle frames spelled `Context::Right`, the rotated
grandparent's children exchanged
(`RbTree::Node(gparent, cid, Color::Red, uncle, rb_reparent(csib, gparent))`),
and `ctx_insert_case3_right_step` in place of the left theorem; the
great-grandparent frame split, including the unfold of its sibling before
`__rb_change_child`, is unchanged. No lemma was added. The frontier report
stays at statement 52, `tmp = parent->rb_left`, now with 35 `break`s and 4
`continue`s complete; `tests/examples.rs` pins it. The reported path is the
node-uncle black arm of the cursor-`Left`, grandparent-`Right` combination
(chunk 6), checked by advancing each of the four remaining stubs one step.
Verify time of the frontier, release build, user seconds: 4.6 with 19
`break`s and 7.0 with 35, measured together at load average 18, so about
0.15 per leaf against 0.14 for chunk 2.

**Chunk 5. Left-right combination: landed 2026-10-02.** The cursor-`Right`,
grandparent-`Left` combination with a black uncle runs case 2's rotation at
the parent and then case 3 to the `break` on 32 leaves: the uncle (node or
empty) times the cursor's left child (empty or a node, for the first
`if (tmp)`) times its right child (for the second) times the
great-grandparent's frame (`Top`, `Left`, `Right` with an empty or a node
sibling). Each leaf refolds the old parent at
`RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid))` before
`parent = node`, the grandparent at
`RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), uncle)`
after `__rb_rotate_set_parents`, and the cursor over both as the new subtree
root; the loop's context binder at the `break` is the great-grandparent's
frame itself, refolded at `node`. `ctx_insert_case2_left_exit_step` supplied
the three whole-tree facts and both children's black roots in the spelling
the arm needed, so the model is unchanged. The frontier report stays at
statement 52, `tmp = parent->rb_left`, now with 67 `break`s and 4
`continue`s complete; `tests/examples.rs` pins it.

The arm needed one tooling fix first, its own pull request: a `step()` in a
`preserve` body was charged to the enclosing `loop`, whose single budget the
sixteenth new leaf exhausted. Verify time of the frontier, release build,
user seconds at load average 5 to 10: 7.1 with 35 `break`s, 11.3 with 51,
14.9 with 67, so 0.26 and 0.22 per leaf for the two halves of this chunk
against 0.15 for chunk 4's shorter leaves; counted work is 77,000 and 67,000
units per leaf against 68,000. The marginal cost of same-shaped leaves does
not grow with the size of the proof.

**Chunk 6. Right-left combination: landed 2026-10-02; the loop rule is not
yet certified.** The mirror of chunk 5 on the cursor-`Left`,
grandparent-`Right` frames, 32 leaves through
`ctx_insert_case2_right_exit_step`, model unchanged. Every path of the loop
body now ends: 3 early `break`s, 96 rotation `break`s, and 4 `continue`s. The
frontier report is gone, and the loop rule itself is refused:
`loop exits reach different states, so they have no common successor: memory,
resource ownership`, which `tests/examples.rs` now pins. The exits hold the
same binders and bytes in different representations (the two binders in
different fold orders, cells cached as concrete cells at some exits and as
run slots at others), and the exit join compared them structurally. That is
fixed: the join now compares cells and merged resources, and joins the record
of automatic storage the rotation exits' helper call leaves
(`mdtests/loop_break_exit_after_a_call_with_a_local_joins.md`). The loop rule
certifies, and `tests/examples.rs` pins the post-loop frontier, so chunk 7 can
start. Verify time of the
frontier, release build, user seconds, back to back at load average 8 to 10:
15.0 with 67 `break`s, 18.3 with the first sixteen leaves here, 27.4 with all
of them and the join. Counted work is 4.63, 5.86, and 6.94 million units, so
the second step adds 1.08 million units but 9.1 seconds: the exit join over
99 exits takes several seconds its work count does not show.

**Chunk 7. Post-loop: `__rb_insert` landed 2026-10-02; `rb_insert_color`
is not proved.** The three early `break`s (root and black parent on both
frames) now state the facts the rotation `break`s already did,
`is_rb_root(plug(c.model, t.model)) == 1`, in-order preservation, and parent
consistency, through `ctx_insert_root_exit` and
`ctx_insert_black_parent_exit` (the root `break` refutes a framed context by
unfolding it for `identity != 0`). All 99 exits state them identically, so
they survive the exit join as ordinary facts, and the post-loop proof folds
the loop's two binders into the result and closes with `step(); simp();`.
No kernel change was needed for the proof.

The contract changed. It produced `ctx_at(root->rb_node, root)` and
`rb_at(root->rb_node)`, which no finite proof can reach: the fixup stops at a
focus with any number of context frames above it, and folding them back to
the root is one `fold` per frame, with no C loop to carry an invariant. It now
produces `rb_tree_at(root)`, a resource over `RbFocus::At(focus, ctx_model,
sub_model)` that owns `ctx_at(focus, root)` and `rb_at(focus)`, and states
the three properties of `focus_tree(tree.model)`, which is
`plug(ctx_model, sub_model)`. The footprint, `root->rb_node` included, and
the whole-tree model are the same. This needs the owner's review: it is the
bottom-up form of D4, and callers that want the root form face the same
unbounded fold.

`rb_insert_color` is proved (2026-10-03). Its only statement calls
`static __always_inline __rb_insert`. By the owner's decision, an inline
helper with a verified contract is called through that contract like any
function, and only a contract-less helper runs its body at the call site
(`docs/reference/language/c.md`). The proof is one call step binding the
context and red subtree to `__rb_insert`'s `consumes` binders. A contract-less
helper with a symbolic loop still runs away instead of failing promptly
(`bugs/inline-helper-symbolic-loop-call-runs-away.md`).

`examples/rbtree-insert/rbtree_insert.click` is now the proof and passes in
the example gate; the `.frontier` file is gone. `tests/examples.rs` keeps the
C's SHA-256 pins and refuses the proof against an in-memory copy of the C
whose root case skips `rb_set_parent_color(node, NULL, RB_BLACK)` (refused
at the proof's claim that the colour bit is black). `click audit` now selects
the same project root as `click verify`, so it can audit a sidecar that
imports a sibling project's model. Verify time, release build, one run at a
time, load average 2 to 4: 30.6 to 32.7 seconds wall, 5.1 GB peak, between
15.5 and 16.0 million counted units; the chunk-6 frontier, on the same build,
also counts between 15.5 and 16.0 million and took 32.4 seconds at load 0.4.
The 6.94 million chunk 6 reported was on a tree without the loop-exit scaling
pull request, which charges work that was not counted before.

### Traversals

`mdtests/rb_first_last.md` already proves `rb_first` and `rb_last`: both
structural results and their positions in the entry tree's in-order sequence,
with the null result and structural ownership preserved on an empty tree. The
assignment-expression parser/lowering prerequisite is delivered for simple
scalar variable targets, including the unchanged `rb_next` guard.

**Chunk 8. `rb_next`.** The complete descent and ascent on the node-keyed
model, on the verbatim body. Certified (2026-10-02): `mdtests/rb_next.md`
proves the successor contract on the unchanged body, with `RB_EMPTY_NODE`, the
descent, the ascent loop (`decreases t;`, `decreases c;`) and the section after
it; `mdtests/rb_next_rejects_a_dropped_context.md` is the negative. One
translation remains: the parameter is declared without `const`, because Click
keeps `const` across the explicit cast in `return (struct rb_node *)node;`
(`mdtests/rb_next_const_signature.md`). Restoring it waits on the importer's
const-dropping cast rule. A predecessor claim is refused only by `simp`
exhausting its budget (`bugs/simp-exhausts-its-budget-on-a-false-list-postcondition.md`),
so there is no wrong-position negative.

**Chunk 9. `rb_prev`.** The mirror of chunk 8. Certified (2026-10-02):
`mdtests/rb_prev.md` proves the predecessor contract on the Linux body, with
`mdtests/rb_prev_rejects_a_dropped_context.md` as its negative. The model's
list lemmas are not symmetric, so it adds `ctx_descends_from_left`,
`ctx_is_left`, `plug_predecessor` and `rb_inorder_first_through_left`. Its
parameter is declared without `const` for the same reason as chunk 8's.

### Erase (D3, D4, D10)

Larger than insert; expect the same cadence of verifier gaps, and expect this
split to be revised once chunk 11 is under way.
Write these proofs with `ensuring` joins from the start; see the
[2026-10-07 handoff](#state-2026-10-07-handoff).

**Chunk 10. Erase model theorems: rebalancing half written 2026-10-02.** One
theorem per `____rb_erase_color` case and side, in the D10 shape of
`ctx_insert_case*_step`, all stated on the loop state the C holds: the cursor
subtree `t` (`node`, possibly empty) is red-black with a black root, and the
context at its parent is valid for a black subtree one level taller,
`ctx_rb(Context::Left(parent, above, pcolor, sibling, up),
Nat::Succ(black_height(t)), Color::Black) == 1` (or `Right`), with the parent
consistency of the whole tree:

- `ctx_erase_case1_{left,right}_step`: red sibling, rotate at the parent. The
  new context is `Left(parent, sibling, Red, rb_reparent(sl, parent),
  Left(sibling, above, Black, sr, up))` (mirrored on the right), which carries
  the same deficit; the new sibling's root is black.
  `ctx_erase_case1_{left,right}_parent_black` gives the parent's colour.
- `ctx_erase_case2_{left,right}_red_exit`: black sibling with black children
  and a red parent; the recoloured subtree makes the whole tree
  `is_rb_root`.
- `ctx_erase_case2_{left,right}_black_step`: the same with a black parent;
  the deficit moves to the parent's subtree in `up`. `ctx_erase_root_exit`
  closes the walk when `up` is `Top`.
- `ctx_erase_case3_{left,right}_exit`: near child red (case 3, then case 4).
- `ctx_erase_case4_{left,right}_exit`: far child red.
- `ctx_erase_{left,right}_sibling_is_node`: the sibling is not empty, so the C
  may read its children.

Every exit theorem states in-order preservation, `is_rb_root`, and parent
consistency on `plug(up, rebuilt subtree)`; every step theorem states them on
the new context. Helpers: `rb_inorder_node_congruence`, `ctx_rb_black_focus`,
`node_color_ok_black_children`, `ctx_erase_case2_left_sibling`. The model
verifies and `click audit` of it passes.

**Black-successor splice model written 2026-10-07.**
`examples/rbtree-model/rbtree_erase_splice.click` adds
`rb_erase_black_successor_splice` for a black minimum with no right child.
It proves all four facts needed before entering erase fixup: the exact
`rb_successor_context` is valid at `Nat::Succ(Nat::Zero)` with a black focus;
plugging its empty hole reconstructs the successor-spliced tree; that context
has consistent parent links; and the local in-order sequence is
`rb_inorder(left) ++ rb_inorder(right)`, dropping the erased root's occurrence.

`rb_minimum` records `Found(identity, original_color, right_child)` without a
parent payload, so reparenting the right subtree preserves the descriptor.
`rb_min_context(tree, up)` follows the C successor descent: an immediate
successor returns `up`; each deeper step pushes a `Left` frame. The final
hole context is computed from `rb_reparent(right, successor)` starting with
`Right(successor, parent, erased_color, rb_reparent(left, successor), up)`.
This describes the model after the parent write; the unchanged C still finds
the successor before writing that parent. The immediate branch's fixup parent
is therefore the successor; the deeper
branch's is the innermost left frame's node. `rb_remove_min_reparent` accounts
for that root-parent write, and `rb_min_context_cut_leaf` identifies the hole
with `rb_remove_min` without assuming the removed leaf was black.

The general context-composition API remains available: `ctx_concat`,
`plug_ctx_concat`, `ctx_consistent_concat`, and `ctx_rb_between`/`ctx_rb_concat`.
The descent theorem carries the outer context as an accumulator, so it also
permits a red root at the boundary inside the right subtree.
`successor_splice_checks.click` covers an immediate successor and a deeper
successor below a red right-subtree root, the exact context/parent shapes,
rejection of zero as the required height, and exclusion of red successors or
successors with a right child from the black-leaf theorem. The red-leaf
successor now has a separate no-deficit theorem, `rb_erase_red_successor_splice`,
establishing whole-tree validity, in-order removal, and parent consistency.
`rb_minimum_child_blackens_without_deficit` proves the balance exit for a
nonempty replacement child. `rb_erase_nonempty_successor_splice` now connects
that exit to the complete successor transplant at any depth, proving whole-tree
balance, exact in-order removal, and parent consistency in the original
context. `rb_remove_min_blackened` supplies the exact model, with checked
context reconstruction, reparenting, contents, and parent-preservation lemmas.
Keep these cases separate from the black-leaf theorem, whose whole spliced
tree still needs fixup.

**Chunk 11. `__rb_erase_augmented`: C coverage complete.**
One general contract, `examples/rbtree-erase/rbtree_erase_augmented.click`,
now covers every exit at every position, and
`rbtree_erase_general_wrapper.click` verifies `rb_erase` on top of it. The
per-case sidecars named in this chunk and in the 2026-10-09 handoff were
retired once those two subsumed them
([design/proof-reuse.md](../design/proof-reuse.md) R2); they remain in Git
history, and their mutations now run against the general unlink.
`rbtree_erase_leaf_wrapper.click` stays because
`examples/rbtree-augmented/rbtree_erase_leaf.click` imports its leaf unlink.
The unchanged C verifies zero/one-child deletion and every immediate and deeper
successor exit, at the root and on either non-root parent link. The deeper
sidecars verify the terminating descent loop, shared splice continuation, and
reconstruction through arbitrary outer contexts. No-deficit cases return exact
remaining models, whole-tree balance, parent consistency, in-order contents,
detached-node ownership, and null fixup. Black-leaf cases retain the exact
one-black-level deficit and return the correct fixup parent for chunk 12.
Mutation checks reject incorrect links, parent/color writes, and fixup results.
Depends on 7 and 10.

**Chunk 12. `____rb_erase_color`, left-sibling cases: in progress.**
The per-case `rbtree_erase_color_*` increments named in chunks 12 and 13 were
retired once `rbtree_erase_color_flips_red_all.click` subsumed them
([design/proof-reuse.md](../design/proof-reuse.md) R1); they remain in Git
history, and their mutations now run against the general proof. The record
below is kept as development history.
`rbtree_erase_color_red_left.click` verifies the first-iteration color-flip exit
for an empty left child, a red parent, and a black leaf right sibling, through
arbitrary outer contexts. The exact whole-root model is balanced and
parent-consistent and preserves in-order contents; all 31 expansion-audit
sites pass. `rbtree_erase_color_root_left.click` covers the black-root exit,
including the null parent cursor, with the same exact-model guarantees and
20 passing audit sites. `rbtree_erase_color_flips.click` now handles
repeated propagation through black parents, with either orientation at every
ancestor, arbitrary black sibling children, and both red-parent and root exits.
It returns the exact balanced,
parent-consistent whole-root model with unchanged in-order contents. Structural
context descent checks every continuing back edge. All 39 audit sites and
four mutation checks pass. `rbtree_rotate_set_parents.click` verifies the
shared incoming-link and packed-word updates for rotations at any tree
position, with 35 passing audit sites. `rbtree_set_parent.click` verifies
reparenting a nonempty subtree of either color while preserving its children,
with 11 passing audit sites and two parent/color mutations.
`rbtree_erase_color_outer_left.click`
now verifies the case-4 left rotation for an empty deficit, empty near child,
and red far leaf under arbitrary outer contexts and either parent color. It
returns the exact balanced, parent-consistent root with unchanged in-order
contents. All 97 expansion-audit sites and four link/color mutation checks
pass. `rbtree_erase_color_outer_nonempty_left.click` also handles a nonempty
near child, preserving its color and child models during reparenting, with
111 passing audit sites and two near-child parent/link mutations. The pinned
C keeps every case. `rbtree_erase_color_inner_left.click` now verifies cases 3
and 4 for an empty deficit, a red inner leaf, and an empty far child, under
arbitrary outer contexts and either parent color. It returns the exact balanced,
parent-consistent root and unchanged in-order contents; all 95 expansion-audit
sites and three link/parent mutations pass.
`rbtree_erase_color_red_sibling_left.click` verifies cases 1 and 2 for an empty
deficit, red sibling, and black near leaf, retaining an opaque far subtree.
It returns the exact balanced root, parent consistency, and unchanged in-order
contents under arbitrary outer contexts; 104 audit sites and three rotation
mutations pass. `rbtree_erase_color_red_sibling_outer_left.click` covers cases
1 and 4 when the red sibling's black near child has an empty near child and a
red far leaf. The two rotations preserve the original opaque far subtree and
return the exact balanced root, parent consistency, and unchanged in-order
contents under arbitrary outer contexts. All 121 audit sites and three
link/parent mutations pass.
`rbtree_erase_color_red_sibling_inner_left.click` covers cases 1, 3, and 4 when
the red sibling's black near child has a red inner leaf and an empty far child.
Its three rotations preserve the opaque far subtree and return the exact
balanced root, parent consistency, and unchanged in-order contents under any
outer context. All 127 audit sites and three inner-link/parent mutations pass.
`rbtree_erase_color_red_sibling_outer_nonempty_left.click` covers cases 1 and 4
with a nonempty near subtree after the first rotation. A verified parent update
preserves its color and children; the proof retains the opaque outer far subtree
and returns the exact balanced, parent-consistent root with unchanged contents.
All 136 audit sites and two near-child parent/link mutations pass.
`rbtree_erase_color_flips_outer.click` combines repeated color flips with a
terminal case-4 rotation in either direction, including a nonempty black focus,
a near subtree of either color, and arbitrary children of the red far node.
It retains the red-parent and root exits, checks structural context descent,
and returns the exact balanced, parent-consistent whole-root model with
unchanged in-order contents. All 21 proofs, 168 expansion-audit sites, and eight
cursor/link/color/parent mutation checks pass.
`rbtree_erase_color_flips_rotations.click` adds terminal cases 3 and 4 in both
directions after propagation, with nonempty focus, far, and inner-grandchild
subtrees. Both grandchild updates preserve their models under their new
parents. The same exact balanced-root, parent, contents, and termination
guarantees hold. All 31 proofs, 300 expansion-audit sites, and eight additional inner-link, grandchild
parent/color, and cursor mutation checks pass.
`rbtree_erase_color_flips_red_exit.click` adds red-sibling cases 1 and 2 after
propagation in both directions. It allows a nonempty focus, retains the old
sibling's opaque far subtree, and reparents its near node with arbitrary black
children. The rotation and color flip return the exact balanced,
parent-consistent root and unchanged in-order contents; every continuing edge
still decreases the context. All 33 proofs, 362 expansion-audit sites, and eight
rotation-link, parent/color, and cursor mutation checks pass.
`rbtree_erase_color_flips_red_outer.click` adds red-sibling cases 1/4 in both
directions after propagation. It admits nonempty focus, near, and far subtrees,
including arbitrary children of the red far node. The two rotations retain the
exact balanced root, consistent parent links, unchanged in-order contents, and
strict context decrease on continuing iterations.
`rbtree_erase_color_flips_red_inner_right.click` extends this to cases 1/3/4
after propagation when the deficit is the right child, including nonempty
focus and rotation subtrees. Its 34 proofs retain exact result, red-black,
parent-consistency, and in-order guarantees.
`rbtree_erase_color_flips_red_all.click` adds the mirrored left-deficit
propagated 1/3/4 case with the same guarantees. Its coverage theorem removes
the case-selection precondition from the repair contract. The complete erase
wrapper integration remains. Depends on 11.

**Chunk 13. `____rb_erase_color`, right-sibling cases, and `rb_erase`.** The
color-flip propagation proof already covers both orientations, including
alternating sides. `rbtree_erase_color_outer_right.click` now verifies the
mirrored case-4 rotation for an empty deficit, empty near child, and red far
leaf, with the same exact balanced-root, parent, and in-order guarantees.
All 97 audit sites and four mirrored link/color mutation checks pass.
`rbtree_erase_color_outer_nonempty_right.click` covers the mirrored nonempty
near child, with 111 passing audit sites and two near-child mutations.
`rbtree_erase_color_inner_right.click` covers the mirrored cases 3 and 4 for a
red inner leaf and empty far child, with the same exact root guarantees,
95 passing audit sites, and three link/parent mutations.
`rbtree_erase_color_red_sibling_right.click` covers mirrored cases 1 and 2 with
an opaque far subtree, 104 passing audit sites, and three rotation mutations.
`rbtree_erase_color_red_sibling_outer_right.click` covers mirrored cases 1 and 4
with the same exact-root guarantees, 121 audit sites, and three link/parent
mutations. `rbtree_erase_color_red_sibling_inner_right.click` covers mirrored
cases 1, 3, and 4 with the same exact-root, parent, and in-order guarantees,
127 passing audit sites, and three inner-link/parent mutations.
`rbtree_erase_color_red_sibling_outer_nonempty_right.click` covers mirrored
cases 1 and 4 with a nonempty near subtree, the same exact-root guarantees,
136 passing audit sites, and two near-child parent/link mutations. The combined
`rbtree_erase_color_flips_outer.click` proof also covers mirrored case 4 after
repeated propagation; `rbtree_erase_color_flips_rotations.click` adds mirrored
cases 3 and 4 with nonempty subtrees. `rbtree_erase_color_flips_red_exit.click`
adds mirrored red-sibling cases 1/2 after propagation with nonempty subtrees.
`rbtree_erase_color_flips_red_outer.click` adds mirrored cases 1/4 after
propagation. `rbtree_erase_color_flips_red_all.click` completes both
orientations of propagated red-sibling cases 1/3/4 with nonempty subtrees.
The unchanged `rb_erase` wrapper now verifies for every leaf deletion: red or
black leaves on either parent link, and the sole root. Its read-only
callback-table splice is checked in `rbtree_erase_leaf_wrapper.click`, which
imports the separately checked general color-repair proof and refolding tactic.
A conditional splice contract supplies either the deficit required by
repair or a balanced context for the no-repair branch. The wrapper returns
the detached node and exact balanced root, with parent consistency and
in-order removal. The left-child and right-child sidecars now verify the
unchanged wrapper for exactly one child at every tree position, including the
borrowed callback-table splice, callback refinements, and context reconstruction.
Two-child wrapper integration now covers every no-repair exit: immediate red-leaf
successors and immediate successors with replacement children, at the root and
on either parent link, plus both exits after deeper successor descent.
The callback tables are borrowed without additional separation preconditions;
the wrappers return the detached node and exact balanced, parent-consistent
root with the remaining in-order contents. The immediate and deeper black-leaf
successor wrappers now import their splice and general repair contracts. The
splices expose a nonempty deficit context and its repair parent; each wrapper
returns the exact repaired root with balance, parent consistency, and the
remaining in-order contents. Wrapper integration now covers all splice cases.
Shared callback and parent-link proofs are imported and checked separately.
Depends on 12.

### Augmented

**Chunk 14. Augmented variants and callbacks.** `__rb_insert_augmented`,
`rb_erase_augmented`, and the propagate/copy/rotate callbacks over an
abstract augmentation. Depends on 7 and 13. The callback and resource
transport it needed landed on 2026-09-15 (one contract interface, one
checked transition per application, dependent clause sets carried across
calls; see [the architecture note](../docs/internals/architecture.md) and
`mdtests/rb_augment_callbacks_helper_*.md`). The 2026-09-14 globals
audit adds `mdtests/rb_augment_callbacks_const_suite.md`: the unchanged const
callback-table caller and a package with read-only fields. It passes under the
shipped stable-view semantics (an earlier candidate-mode refusal was resolved
before the cutover recorded in
[the stable views record](../docs/internals/stable-views.md)), while the
broader [global initializer issue](global-variables.md) is P2. Keep the table
const and preserve the callback guarantees; the no-op fixture is not evidence
for the complete mutation-capable augmentation proof.

The public entry-point integration now verifies in `examples/rbtree-augmented`.
`__rb_insert_augmented` and `rb_insert_augmented` reuse the checked insertion
contract, and `__rb_erase_color` reuses the general repair contract.
`rb_erase_augmented` is checked for leaf deletion at every position, including
both the repair and no-repair paths. The C wrappers are verbatim pinned extracts;
contracts retain balance, parent consistency, in-order contents, and detached
ownership. This increment still uses callbacks without writable footprints;
metadata ownership and its augmentation invariant remain unfinished.
`rbtree_subtree_size.click` establishes the concrete mathematical count model:
nonnegative sizes, reparenting invariance, and both rotation callback updates
(copy the promoted root's summary and recompute the demoted node). The concrete `SizedTree` ownership model now connects C size fields to the
mathematical subtree count under checked machine-integer bounds.
`rbtree_size_recompute_model.click` restores that invariant through the unchanged
`compute_size` helper. `rbtree_size_rotate_model.click` restores it through the
unchanged size rotation callback, in both directions and all four nullable-child
configurations, assuming the structural links and parent tags already rotated.
It preserves the erased shape and returns a recursively sized tree.
Recomputation also exports the early-stop implication: a nonzero return means
the cached size did not change. The unchanged propagation body now verifies
for its first visited leaf, including both early break and parent advance to
an exclusive stop. Loop resources retain entry-bound pointer and scalar
parameters across cursor changes. The ancestor model now retains cached sizes
and sibling subtrees, preserves erased shape on reconstruction, and proves that
unchanged focused size permits stopping with every remaining ancestor count
correct. Recursive ownership certification and recomputation establish the
count-validity predicate used by this theorem; recomputation preserves both
child models. Owned ancestor frames and a checked recursive reconstruction
tactic now rebuild the valid sized tree on early stop. Path and result models
carry the reconstruction root without adding a C parameter to the callback.
`rbtree_size_propagate_tree.click` now connects these helpers to the unchanged
arbitrary-length C loop. It checks both exits, invariant preservation, and
termination by context depth, then returns ownership of the valid sized tree
with its original root and erased shape and recursively valid counts.
Checked projection of the loop exit disjunction establishes that the joined
walk is finished. `rbtree_size_callbacks.click` packages these checked contracts in a borrowed
callback table. Its copy dispatcher preserves independent structural ownership;
its propagation dispatcher returns the whole repaired sized tree. Its rotation
dispatcher selects the left or right dirty model and returns a valid sized
subtree, with separately checked interfaces for both directions. The callback
bodies remain unchanged. The concrete sized insertion cases below check
selected writable callback-table paths; general insertion and writable erasure
integration remain unfinished.


### Pinned source

The in-repository import fixture is a demonstration arrangement, chosen for
expedience; work that uses imports is expected to move out of this
repository. Click imports only the checked dependency closure of the verified
rbtree functions, about 80 of the 2,575 file-scope declarations in the
preprocessed unit, and makes no claim about the rest. A declaration inside
the closure that is unsupported is rejected, not dropped. Export storage and
`.export_symbol` assembly are outside the closure and outside the claim.
The measured inventory is in
[kernel-scale-preprocessing.md](kernel-scale-preprocessing.md).

Landed or in the merge queue: variadic prototypes retained as uncallable
declarations, and the
pinned closure `integrations/linux-rbtree/` with its gate test and measured
frontier. `typeof`, statement expressions, and `__builtin_expect` were
already supported.

Chunks 15 to 20 are independent of each other but edit the same parser, so
they run serially. Each moves the first rejection pinned in the gate.

**Chunk 15. Character-literal escapes.** Octal and hexadecimal escapes; the
current first rejection is `'\001'` at `include/linux/printk.h:21`.

**Chunk 16. Declaration-only attributes.** `__gnu_inline__`, `__unused__`,
and `no_instrument_function` on `static inline`, with near-miss negatives;
`gnu_inline` on a non-static inline stays rejected.

**Chunk 17. Unnamed parameters** in body-less prototypes (eight in
`rbtree.h`).

**Chunk 18. Static non-inline file-scope functions**
(`rb_left_deepest_node`).

**Chunk 19. Qualifier and conditional typing.** The const forms in `rb_next`,
`rb_prev`, and the postorder functions, and the conditional-operator type in
`__rb_erase_augmented`, by the actual C rules.

**Chunk 20. `compiletime_assert` and `__builtin_constant_p`.** Block-scope
`extern` declarations with `noreturn`/`error`, and a constant-p semantics
under which the code Click verifies in `rcu_assign_pointer` is the code the
pinned compiler compiled.

**Chunk 21. Checked dependency-closure projection.** Depends on 15 to 20.

**Chunk 22. Recorded compiler-option profile and lock.** Accept a recorded
option only where ignoring it cannot make Click accept what the compiler
treats differently; then a real import lock replaces the negative gate.
Depends on 21.

**Chunk 23. Pinned inline helpers.** The actual `rbtree.h` and
`rbtree_augmented.h` inline bodies as called from the pinned source, per
[linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md). Depends on
22.

**Chunk 24. Attach the sidecars to the pinned translation unit** and replace
the verbatim-copy fixtures with the pinned regression. Depends on 9, 14, and
23.

## Structural termination audit, 2026-09-14

Audited at `61a3ce92`. The separate `structural-loop-termination` issue is
retired: its missing-language-feature diagnosis predates A4 and the subsequent
loop work. The remaining algorithm proofs stay P1 in C3, C4b, and C5 here;
retiring the duplicate issue does not establish termination of unfinished
insertion, erase, or successor/predecessor proofs.

The implemented spelling is `decreases sub;` for a loop resource binder and
`decreases list(node);` for a function resource measure. The back-edge rule is
**strict contained descent**, including multiple exposed child layers, rather
than only one direct child. It compares the finite inductive model carried by
the rebound instance with submodels named by the exact resource definitions
and the selected constructor premises. A fresh instance name does not by
itself prove progress. Kernel `loop_structural_descent_failure` in
`src/kernel/loops.rs` supplies the check for loop execution and the proof-object
loop join in `src/surface/proof/proof_object/execution_statements.rs`.

| Original requirement | Current evidence and remaining scope |
| --- | --- |
| Descend through children without a C counter | `mdtests/rb_first_last.md` and `examples/modeled-binary-tree` carry a subtree measure. |
| Ascend through a recursive context | `mdtests/rb_ascending_walk_to_root.md` carries a context measure while rebuilding the focused tree. |
| Continue after consuming context layers | `mdtests/loop_body_continue_back_edge.md` checks the explicit `continue` back edge (with a numeric measure); `loop_decreases_strict_descendant.md` checks one- and two-layer descent. These are component regressions, not completed rebalancing proofs. |
| Reject staying put | `mdtests/loop_decreases_rejects_same_instance.md` reaches the descent refusal. |
| Reject an unrelated node | `mdtests/loop_decreases_rejects_unrelated_node.md` rejects the missing owned instance at the rebound cursor; it is an ownership/binder regression, not an isolated test of the ancestry comparison. |
| Reject recreating a consumed layer | The audit adds `mdtests/loop_decreases_rejects_rebuilt_layer.md`: unfold the recursive layer, refold it under a fresh name with the same model, then close the back edge. Folding succeeds and descent is refused. Removing only the decreases clause verifies the same proof, isolating the ranking failure. |

The remaining integration acceptance is unchanged C with a checked measure on
**every continuing back edge** of the required algorithms. In C3a the
recolouring `continue` must return `up.up` with all invariants; C3b's rotation
`break` paths must establish their exit guarantees and do not need descent
across an edge that exits. C4b must finish the actual `rb_next`/`rb_prev`
descent/ascent paths, and C5 must cover erase/rebalancing, including any
rotation followed by a continuing edge in the unchanged source. The synthetic
component tests do not substitute for those algorithm proofs. Do not add a C
counter, bounded unrolling, a heap-size assumption, or a rewritten control-flow
path to satisfy termination.

There is no separately demonstrated missing structural-ranking operation to
implement next. Resume the corresponding rbtree proof package and reduce any
new kernel obstruction it exposes. Preserve the same-instance, unrelated-node,
and rebuilt-layer negatives. Concurrent-reader termination and broader well-founded resource families
remain outside this sequential MVR obligation.

Audit validation: all four `loop_decreases` fixtures pass under ordinary and
candidate stable-loan semantics. Ordinary `click audit` checks all five smart
sites in `loop_decreases_strict_descendant.md` and all four in the
`continue` structural-measure fixture. The rebuilt-layer negative reaches
the descent refusal; its control without the measure verifies. The full unpiped
`scripts/check.sh` passes, including the existing traversal/ascent fixtures and
the new negative. This is an evidence audit of the stated milestone, not an
exhaustive soundness or scaling audit of the resource kernel.

The maintained language explanation is
[structural loop measures](../docs/concepts/loops-and-invariants.md#structural-loop-measures).

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
  establish their respective guarantees, including structural termination on
  all continuing back edges as recorded in the audit above.
- Small positive and negative rotation and insert/erase regressions (synthetic
  or on the pinned source), required MVR model proofs, and
  `scripts/check.sh` pass.

Integer specification coverage is landed and documented in
[the mathematical-integer internals](../docs/internals/mathematical-integers.md);
this MVR model work has no pending dependency on the retired Integer P1
issue. Related: [algebraic-data-types.md](algebraic-data-types.md).

`rbtree_size_metadata.click` now checks `split_sized_tree`: full `sized_at`
ownership separates into the original structural `rb_at` and a cache-cell-only
`sized_metadata_at`, preserving both models. Its child indices are pure
model-derived C pointers, so metadata ownership does not depend on reading
links that structural callbacks may change. `join_sized_tree` now reassembles structural and metadata ownership when
their shapes agree and the metadata counts are valid, preserving the full
`SizedTree` model. Its recursive proof and all nine split/rejoin expansion
sites verify. Common-base pointer disequalities now remain available through
normalized offset comparisons in the shared graph. Using the writable concrete
callback table in the augmented entry points remains unfinished.
`CopySizedStructure` additionally certifies that the unchanged size-copy
callback preserves separately owned structural trees while updating its
metadata cells; its execution theorem and expansion audit pass.

`rbtree_size_insert.click` checks the no-parent branch of the unchanged insertion
body and both augmented insertion wrappers with full sized-tree ownership.
It recolors a red root black while preserving the child models and cached sizes,
and accepts any typed callback because this branch makes no callback call.
This is a root-case boundary, not the ancestor/rotation integration or a new
balancing theorem. The constructor validation paths now agree with lowering
that literal `0` can initialize a known pointer-valued model field.

The complementary black-parent exit and both wrappers now verify in
`rbtree_size_insert_black_parent.click`. They preserve the focused sized model
and the full ancestor tag, with no callback premise. This proves both immediate
insertion exits; continuing ancestor/color-flip and rotation paths remain.


`rbtree_size_insert_rotation.click` now checks a left-left three-node rotation
at the root and both augmented insertion wrappers. It calls the indirect
writable callback through the proved `RotateTreeRight` contract and returns the
expected black-root/two-red-leaf shape with recursively valid cached sizes.
The original insertion C is unchanged. Other rotation shapes, color flips,
arbitrary ancestor contexts and writable erase integration remain.


The mirrored right-right root case and both wrappers also verify in
`rbtree_size_insert_mirrored_rotation.click`, using `RotateTreeLeft` for the
writable callback. All 17 expansion sites in each single-rotation sidecar
pass. Color flips, arbitrary ancestor contexts and writable erase integration
remain; double-rotation progress is described below.

`rbtree_size_model_unique.click` now proves that two recursively count-valid
`SizedTree` values with equal erased shapes are equal, by induction on one
model and exhaustive constructor matching on the other. This supplies the
exact model transport needed between two writable rotation callbacks.


`rbtree_size_insert_double_rotation.click` checks the left-right three-node
root insertion and both augmented insertion wrappers with writable callbacks.
The first left rotation repairs the parent/focus sizes; model uniqueness
identifies that returned subtree before the outer right rotation. The second
callback repairs the final root and demoted grandparent sizes. The result owns
the exact black-root/two-red-leaf shape with recursively valid subtree counts.
The Linux C is unchanged. Color flips, arbitrary ancestor contexts, and
writable erase integration remain unfinished.


`rbtree_size_insert_mirrored_double_rotation.click` checks the mirrored
right-left root case and both wrappers. It repairs the inner right rotation
before the outer left rotation, returning a black focus root with the
grandparent on the left and the original parent on the right. Both double
rotation directions now check two writable callbacks in sequence. Together
with the single rotations, all four three-node root rotation shapes are
covered with recursively valid cached sizes.


`rbtree_size_insert_color_flip.click` and
`rbtree_size_insert_mirrored_color_flip.click` check the four-node color-flip
path in both orientations, including `__rb_insert` and both augmented wrappers.
The red parent and uncle become black, the focus moves to the grandparent,
and the loop continues before blackening that new root. The owned
`sized_context_at` chain has two ancestor frames before the flip and none
afterwards; its actual `sized_context_depth` supplies the decreasing measure.
All cached sizes and links are preserved, and the returned resource describes
the exact recolored sized tree. This path invokes no callback and accepts any
correctly typed rotation pointer. These are root-reaching flips; continuing
through arbitrary ancestors and writable erase integration remain unfinished.


`rbtree_size_insert_context_color_flip.click` and its mirrored counterpart
extend the four-node flip beneath a nonnull black parent with an arbitrary
owned outer ancestor context and arbitrary sibling trees. The loop moves past
the two inner frames, stops at the black parent, and uses the previously
proved `restore_sized_context` to return the whole root tree. The postcondition
states its exact model as the unchanged outer context filled with the recolored
subtree; cached counts and links are preserved throughout. The ranking measure
is the actual context depth, reduced by two on the continuing path. This covers
a single flip followed by a black-parent exit, not repeated flips through red
ancestors or non-root rotations.


`rbtree_size_change_child.click` now checks the insertion translation unit's
`__rb_change_child` helper using a file-qualified contract. It replaces a
root, left-parent, or right-parent incoming link while retaining the exact
owned `SizedContext`, every ancestor cache, the old focus cache, and the old
focus parent/color word. A nonempty sibling is separated using its existing
ownership. This supplies the sized incoming-link interface for non-root
rotations.


`rbtree_size_rotate_set_parents.click` also checks the selected insertion
helper for root, left-parent, and right-parent contexts. It transfers the old
packed parent/color word to the promoted node, sets the demoted node's new
parent/color word, and calls the checked sized incoming-link helper. The
ancestor model and caches and the demoted node's cache are preserved. Full
non-root insertion must still compose this helper with the writable rotation
callback and whole-context restoration.


`rbtree_size_link_distinct.click` derives the promoted node's inequality with
the outer parent from separated owned words in either ancestor orientation,
while preserving the incoming-link model. The sized parent-update helper now
calls it internally and no longer requires callers to supply this disequality.
C comparisons and `assumption()` share the indexed nonempty separation rule;
full non-root insertion still needs callback composition and context restoration.


The sized left-left insertion rotation now composes the parent-update helper
with its writable callback under an arbitrary owned outer context, and both
augmented insertion wrappers verify. The result refolds the repaired subtree
through its preserved ancestor context and owns the whole root tree, with its
model identified by `sized_plug`. Its eighteen-site expansion audit passes; the
other non-root rotation shapes remain.


The mirrored sized right-right context rotation also verifies through both
wrappers and restores the whole root model. Its eighteen-site audit passes.
Both context cases use the shared black-parent-word lemma; non-root double
rotations remain.


Both sized non-root double rotations now compose their two writable callbacks
with the checked incoming-link helper and whole-context restoration. The
left-right and right-left entries and their augmented wrappers retain the exact
outer context and return whole-root ownership, with the model related by
`sized_plug`. All four three-node rotation shapes are now covered under arbitrary
owned ancestor contexts. Repeated flips through red ancestors, general insertion
subtrees, and writable erase integration remain unfinished.


Shared sized recoloring and color-flip model operations now preserve cached
values and recursive count validity for arbitrary subtrees, with checked bridges
to the existing structural model operations. Root-only insertion uses the shared
recoloring definition. These lemmas prepare general color-flip propagation;
the existing C flip sidecars still cover their documented finite cases.


The black-parent stopping case now restores whole-root ownership for arbitrary
focused and sibling subtrees and either parent orientation, through both
augmented wrappers. Its contract returns the root link and the exact original
`sized_plug` model. This supplies the general stopping boundary for subsequent
color-flip propagation proofs.


Both non-root color-flip sidecars now accept arbitrary owned child subtrees of
the red focus, with symbolic valid cached sizes at the focus, parent, and
grandparent. The loop carries the original focused model and cache values;
explicit count equalities connect the opened ancestor frames to the recolored
models. Both orientations and both augmented wrappers verify, and both
12-site expansion audits pass. Whole-root ownership, exact `sized_plug` models,
and context-depth termination are preserved without changing the Linux C.
Both sidecars now also accept an arbitrary owned other child of the parent and
arbitrary owned children of the red uncle. Parent and grandparent cache values
remain symbolic. The three count obligations in each orientation close with
`assumption()` through the shared Integer/model equality classes, without
explicit alias rewrites. Each sidecar verifies all three insertion claims.
Repeated color-flip propagation through a red outer ancestor and writable erase
integration remain unfinished.

The sized subtree and ancestor resources now retain the full pointer recovered
from each packed parent word, matching the base rbtree resource's representation
invariant. Numeric address equality alone does not retain pointer designation
and bounds. Both context color-flip proofs explicitly transport the unchanged
left/right child inequalities across the recoloring writes. All six insertion
and wrapper claims verify, and both eighteen-site expansion audits pass. The
four context/size helper tactics and two sized-model theorems also verify.
Repeated-flip model definitions now check with nominal model-pointer typing;
the owned cursor and its whole-tree restoration helper are being developed
before the general C loop proof.

Pure helpers now check their declared return types at definition boundaries.
Recursive pointer getters use those checked interfaces, with the existing
termination checks, so `rb_min_parent` retains its model field's object class.
All ten sidecars in the default `rbtree-model` project verify. This removes the
getter typing blocker without adding proof steps to the affected theorem.

The repeated-flip cursor and whole-tree restoration tactic now verify. The
boundary sidecar checks both ways a chain stops: blackening the root or exiting
beneath a black parent, in either ancestor orientation. It returns whole-tree
ownership with the exact chain-result model, including through both augmented
wrappers, without changing the Linux C. Applying restoration exposed a call
boundary bug: named output arguments were evaluated before sibling produced
memory clauses supplied their read authority. The fix constructs those primitive
outputs once and carries the same facts into the return transition. A reduced
regression covers user tactics and C calls, including reversed output order.
The general chain sidecar now verifies all continuing LL/LR/RL/RR cases,
arbitrarily repeated and mixed, followed by either stopping boundary. Both
augmented wrappers return whole-root ownership, the exact chain-result model,
and recursively valid cached sizes. A separate induction proves preservation
of the complete in-order sequence. The proof uses pre-write color facts and
explicit transport across recoloring stores. The loaded-uncle comparison now
uses shared numeric address classes for its scoped separation evidence;
regressions cover checked aliases, scope, withdrawal, and scalable lookup.
General rotation subtrees, chains ending in a rotation, and writable erase
integration remain unfinished.
