# User-defined tactics (design)

This design record covers user-defined tactics: proof procedures declared in
Click, certified once, and applied in C proofs.

Status: delivery steps 1, 2, and 5 are implemented: declarations,
certification, application in C proofs before function exit, self-recursion
ranked by numeric measures or named structural binders (see
[User-defined tactics](../reference/language/index.md#user-defined-tactics)),
and the consumer, `refold_to_root` in `examples/rbtree/rbtree-insert`, which gives
`__rb_insert` its root-form contract. Steps 3 and 4 remain.

## Why Click needs them

A proof moves ownership only one layer at a time, with `fold` and `unfold`.
That suffices whenever the number of layers is fixed by the proof's text. It
fails when the number is a symbolic quantity that the C does not walk. The
Linux insert fixup `__rb_insert` stops at an arbitrary depth, and its natural
contract hands back the whole tree at `root->rb_node`. Producing that means
one `fold` per context frame above the stopping point. No finite script writes
that many folds, and the C has no loop or recursion that climbs back up for a
proof to ride on. The erase design meets the same wall when it merges its
spine back into an ordinary context.

Facts about models already handle unbounded depth: pure theorems prove
`plug(ctx, sub)` red-black by `induct`. The gap is ownership. A user-defined
tactic closes it with recursion. Its contract is proved once, by induction on
a measure, where the recursive application is the induction hypothesis; each
later application is one checked step. Without recursion a user tactic only
abbreviates steps a proof could already write, which is a convenience; with
recursion it makes true contracts provable that are unprovable today.

## The idea

A tactic is a checked rule from one proof state to another. It consumes some
resource instances and facts and produces others. It changes the proof's
resource context and fact context, never memory and never C state.

```text
tactic refold_to_root(focus: struct rb_node*, root: struct rb_root*) {
    consumes c: ctx_at(focus, root);
    decreases ctx_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == plug(old(c.model), old(t.model));
} by {
    match c.model {
        Context::Top => { ... fold the root cell and t into rb_root_at(root) ... },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            ... derive rb_parent_is(t.model, identity) from parent consistency ...
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { ..., left: t, right: s });
            ... establish the measure's descent ...
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
        },
        Context::Right(...) => { ... mirrored ... },
    }
}
```

The full proof is in `examples/rbtree/rbtree-insert/rbtree_insert.click`.

A C proof applies it with an explicit binder map, like a call step but with no
C statement:

```text
let { tree: tr } = refold_to_root(node, root, { c: c, t: t });
```

## Declaration

- **Parameters.** Any Click type: C scalars and pointers, `Integer`, `Nat`,
  spec enums and models. A non-C parameter is a logical parameter, as a
  theorem's is; nothing about it is C storage.
- **Clauses.** The contract clauses of a function: `consumes`, `produces`,
  `owns` (held in and out), `views`, `requires`, `ensures`. `old(...)` reads
  the proof state before the application. `exceptional ensures` and
  `constructs` do not apply, since no code runs.
- **Termination is required.** `diverges` is refused. A non-recursive tactic
  terminates by construction, as a straight-line C function does. A recursive
  one must declare an expression `decreases` measure, written after the
  binders it reads. A non-terminating recursive tactic would make its own
  contract an unproved assumption and could prove false. A body may apply
  itself and earlier tactics only, so tactics are never mutually recursive.
- **Language neutrality.** Nothing in a declaration names a C construct
  beyond the pointer and scalar types the shared contract language already
  expresses. A tactic may live in a theorem-only `.click` file and be imported
  by C, C++, and Rust sidecars alike: all three frontends lower to one execution
  IR and share the kernel, and a tactic is defined over that shared proof
  state.

## Proof body

The `by` block is an ordinary proof at a fixed execution point. It may use
`match`, `unfold`, `fold`, `have`, theorem application, applications of
tactics (itself included), `if`/`cases` on propositions, and smart tactics
such as `close()`. It may not use `step`, `step_until`, `branch`, `loop`, or any
other tactic that advances C. The proof ends when every produced instance and
every `ensures` is established; there is no exit statement to step to.

A recursive application inside the body is the induction hypothesis. It owes
the measure's descent at that application, as ordinary preconditions: the
measure at the application is nonnegative and strictly smaller than at entry.
These are emitted by the same recursion anchor that ranks a recursive C
function's expression measure.

A bare numeric parameter also uses these ordinary application obligations.
A structural measure (`decreases x;`) ranks the instance passed for that
resource binder: its model must be strictly contained in the entry model,
through constructor arms established on the proof path. Unfolding the entry
instance exposes the child to pass, as with structural loop measures.
Anonymous resource applications use the finite-witness evidence retained by
the resource operations that supply their calls.

## Application

- **Where.** Anywhere a proof has a current state: a C function proof before
  and after its exit, loop `initialize` and `maintain`, `branch` and proof
  `if` arms, other tactic bodies, and pure theorem proofs when the tactic has
  no resource clauses.
- **What it checks.** The map selects held resource instances of the
  declared types and arguments. The step driver proves argument evaluation
  obligations and instantiated `requires` clauses at the caller's frontier
  using the existing statement obligation proofs.
- **What it does.** Removes the consumed instances, adds the produced ones
  under the output names, adds the `ensures` facts. Memory is unchanged, and
  every fact the proof holds about cells remains valid.
- **Classification.** The application is a checked step. `click expand`
  keeps the application and writes the proofs of its call-site obligations.
  `click audit` inventories the smart sites inside tactic bodies like those
  in any proof.

## Kernel

There is no new certification judgment, and one new checked proof event, the
application.

- **Certification.** A tactic is certified as the contract of a procedure in
  the shared kernel IR whose whole body is `return;`, with an empty write
  frame. A procedure that runs no code changes nothing but the resources its
  contract transfers, so its contract holds of a proof state exactly when the
  tactic's does. Certifying it reuses every existing check: the contract's
  entry state, resource transfer, recursion hypotheses, termination, rule
  packaging at the completed contract root, and the audit's targeted runs. The
  surface proves it with the tactic's script followed by the one `return`
  step and one direct closure per claim and per contract-closing goal, so the
  script itself must leave each produced instance held and each `ensures`
  available on every live path. This ending does not depend on the implicit
  closer, so a tactic's expansion, which leaves it out, is checked the same
  way with that closer off. The script runs no code: it may not `step`, but a
  `fold` may prove its instance facts with `by { ... }`.
  A terminal `contradiction` in a proof `match` arm instead refutes that
  path with a checked fact and its negation; no return or postcondition
  suffix is added there, and expansion preserves the refutation. The IR is the one all
  three frontends lower to, so nothing about this is specific to C.
- **Termination.** Each `TacticApplication` event names the tactic it
  applied. The kernel collects those names from the checked traces into the
  certified claims and the verified rule (`applied_tactics`), and the
  termination call graph reads them as the rule's call edges, since its body
  has none. A recursion carried by such an edge owes its numeric or modeled
  structural descent at the application, through the ordinary recursion anchor.
- **Application event.** `CheckedExecutionEvent::TacticApplication` records a
  tactic application at a frontier. `prepare_verified_tactic_rule` requires a
  procedure whose body is `return;` and prepares the transition from its
  verified rule or scoped assumption through the ordinary call boundary.
  The step driver proves the requirements at the original frontier before
  the kernel appends the event. The retained transition applies without a
  C statement.
  The empty write frame is what leaves memory unchanged: the boundary havocs
  only the frame, and the frame was certified against the body. Trace
  certification connects the event's before and after states like any other
  resource event.

The trusted addition is the application event and its body check. All
reasoning inside a tactic body reuses existing checked steps.

## Delivery

One design, delivered in pull requests on it:

1. Declaration, parsing, validation, certification of a non-recursive tactic,
   and application in C proofs, with the event and no-havoc transfer. The
   tactic expand/audit inventory and every per-variant tactic table join here.
2. Recursion: self-recursion ranked by numeric measures or named structural
   binders, the tactic call edges, and refusal of unranked recursion,
   and `diverges`. Anonymous resources use retained finite-witness evidence.
3. Cross-backend regressions: one imported tactic applied in a C proof, a C++
   proof, and a Rust proof, with a refusal in each.
4. Click-typed logical parameters (`Integer`, `Nat`, models), application in
   pure theorem proofs, mutual recursion, and lexicographic measures.
5. The consumer: `refold_to_root`, and `__rb_insert` restated to produce
   `rb_at(root->rb_node)`.

## Regressions owed

- Positive: a non-recursive tactic, a recursive structural refold over a
  context chain of unknown depth, an expression-ranked recursive tactic, and
  application before and after a function's exit and in a loop body.
- Refused: an application missing a `requires`; a binder bound to the wrong
  resource type or an instance not held; reuse of a consumed instance after
  the application; a recursive application whose measured instance is not a
  strict descendant; a tactic without `decreases`; a tactic declaring
  `diverges`; a `step` inside a tactic body.
- Memory: a fact about a cell outside the tactic's footprint, and one inside
  it, both survive an application unchanged.
- Scaling: certification work linear in the body; application work linear in
  the binder map and the `ensures`, independent of how deep the tactic's
  recursion is.

## Decisions

- Application is written like every other tactic, `name(args)`, with an
  optional binder map and output pattern:
  `let { tree: tr } = refold_to_root(node, root, { c: c, t: t });`. `apply` stays
  for applying theorems, which are not tactics. A tactic name may not shadow a
  built-in tactic.
- Delivery follows the order above: recursion before Click-typed logical
  parameters, since the rbtree consumer needs only C-typed parameters.
