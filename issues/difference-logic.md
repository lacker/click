# Difference logic: the fast path for arithmetic requirements and conditions

Priority: P1.

Soundness: not soundness. This replaces how the kernel decides arithmetic
conditions during simple checking, not what it accepts: every answer is a
consequence of the path's own condition facts by difference-logic rules, the
same facts the current decision reads. The new structure is kernel code and
is held to the same agreement tests as the decision it stands in for.

## Why this is P1

[simplify-step.md](simplify-step.md) requires every simple tactic's
requirements to be closed by a fast path ("an exact or indexed lookup, or a
bounded local kernel decision about the affected operation") or by an
expandable implicit `auto`, and its final step removes the hidden search. It
notes the largest route its census does not count yet: the kernel's own
condition evaluation, which calls the general condition decision
`PureFactContext::decide` on every C comparison, overflow check, and pointer
bound it evaluates. That decision searches the whole path. Removing it needs
a fast path that still answers the ordinary questions; this issue builds it.

## The violated invariant

A simple step's cost must not grow with unrelated path facts
([verification efficiency](../docs/internals/verification-efficiency.md)).
`bugs/sequential-loop-clause-grows-with-earlier-loops.md` shows it does:
each earlier loop leaves facts about its own copy of the loop variable
(`0 <= i_j`, `i_j <= 4`, `!(i_j < 4)`), all meeting at the constant bound.
Evaluating a later loop's `i < 4`, `has_lower_bound_above` takes every `i_j`
filed under `4` as a candidate and runs a nested decision for each, so a loop
clause costs about the square of the loops before it.
[#831](https://github.com/clicklang/click/pull/831) made the order walk
inside those decisions cheaper; the candidates, and the other rules that read
the whole path, remain. The intended regression is that shape:
`python3 scripts/step-scaling-hunt.py loops --sizes 8,16,32,64`, whose largest
loop clause charges 15,094, 58,744, 235,898 and 949,628 units today.

## What the decision is mostly used for

Measured on `cb2bf3c` with a temporary switch that made the executor decide
conditions only by exact lookups and a condition's own form
(`decide_with_facts`, `condition_is_decided`, and the consistency check when a
path fact is added), smart tactics keeping full reasoning, then with a
difference-logic oracle standing in for the general decision:

| Executor decides by | mdtests failing (of 3,853) | examples failing (of 50) |
| --- | --- | --- |
| general `decide` (today) | 0 | 0 |
| exact lookups only | 622 | 28 |
| exact + per-value bounds | 236 | 18 |
| exact + difference logic | 58 | 9 |

No refusal test became accepted under any of them.

Most of the general decision's use is one-step arithmetic about the operation
itself: `i + 1` cannot overflow given `i < 4`, `bytes[index]` is in bounds
given `index < length`, `n - 1` is defined given `0 < n`. Branch pruning is a
small share. All of it is difference logic: constraints `x - y <= c` and
constant bounds.

What the 58 still need:

- Bound tightening at the end of a range: `-x` and `x / y` need
  `x != INT_MIN`, which with `x >= INT_MIN` is `x >= INT_MIN + 1`.
- Shifts by a constant (`x << 1` is `2 * x`), and the range of a narrow type
  (`int8`, promoted `uint8`) as a node's initial bound.
- Bounds of loaded values that come from memory or resource facts rather than
  condition facts (`sum + node->value`).
- Pointer questions (alignment, disequality, deciding a pointer comparison),
  which belong to the equality graph's pointer side, about a dozen.
- Loop-invariant closures that met infeasible paths the weaker pruning left
  in, about eight; not yet diagnosed.

Seven of the nine failing examples are Rust imports, which use conversions
(`usize`, `u64`) the oracle did not model.

## Design

`DifferenceGraph`, beside `EqualityGraph` and keyed by its classes.

- **Nodes** are `int32`, `int64` and `uint64` equality classes. Their values
  are mathematical integers, so nodes of different widths can be related
  (sign extension is an exact link).
- **Edges** are constraints `x - y <= c`. A true order or equality fact is one
  or two edges; a false one is its negation. A constant bound is an edge to
  the zero node, so a constant is never a node: facts about unrelated values
  never meet at a shared constant.
- **Wrapping.** A term `x + k` is linked to `x` (`t - x <= k` and
  `x - t <= -k`) only once `x`'s bounds show the sum cannot wrap. That is the
  same question as the overflow check, answered from the same bounds.
- **Insertion** propagates bounds along the new edge's neighbourhood with a
  bounded worklist, so `x < y` with `y <= 100` records `x <= 99` when it is
  assumed. A negative cycle is a contradiction; a zero-weight cycle is an
  equality, passed to `EqualityGraph`. A merge there merges nodes here.
- **Queries** are reads: an order or overflow question compares stored
  bounds, and a relation between two values reads their edge or a bounded
  path inside their own component. Neither depends on facts about other
  values.
- **Persistence.** Like the equality graph, it is shared between proof
  branches and extended in work proportional to the delta.

Out of scope: `x + y <= c` between two variables, multiplication and division
of two variables, and other non-linear arithmetic. Those stay with smart
tactics and implicit `auto`.

## Plan

Each step is its own pull request.

1. **The structure (landed).** `DifferenceGraph`
   (`src/kernel/difference_graph.rs`) with insertion, interval propagation,
   wrap-checked links, contradiction detection, and queries for orders,
   equalities and add/subtract/multiply overflow. Nodes are keyed by term;
   an equality is two edges. It is tested on its own and consulted nowhere
   yet: `decisions_hold_in_every_model_and_are_complete` enumerates every
   model of generated bounded fact sets and requires each answer to hold in
   all of them and each entailed order to be answered, and
   `work_is_independent_of_unrelated_bounded_values` pins insertion and
   query work at 2, 0 and 1 units beside 16 to 1,024 unrelated values.
2. **Fast path in condition evaluation.** Maintain the graph in the fact
   context as conditions are assumed, keyed by the equality graph's classes,
   and have the kernel's condition evaluation ask it before the general
   decision. Count, as [simplify-step.md](simplify-step.md)'s census does,
   the decisions only the general decision makes.
3. **Close the gap.** Range-end tightening, constant shifts, narrow-type
   ranges, load bounds, and routing pointer questions to the equality graph,
   each lowering that count.
4. **Remove the general decision from simple checking.** A condition the fast
   path leaves undecided keeps both branches, and an arithmetic requirement it
   leaves open goes to implicit `auto`, as
   [simplify-step.md](simplify-step.md) decides. Rerun the corpus, migrate the
   proofs that change, and close the loop bug.

## Acceptance criteria

- Simple checking decides arithmetic conditions and requirements without
  `PureFactContext::decide`; the census of such decisions is zero.
- The `loops` shape's largest loop clause is constant in the number of
  earlier loops at four sizes, as a deterministic regression.
- Insertion and query work in `DifferenceGraph` is constant in unrelated
  facts at four sizes.
- Generated-case tests show `DifferenceGraph` never decides a condition the
  facts do not entail.
- `scripts/check.sh` passes, `bugs/sequential-loop-clause-grows-with-earlier-loops.md`
  is deleted, and `docs/internals/verification-efficiency.md` describes the
  structure.

## Not in scope

- Non-linear arithmetic and relations between sums of variables.
- Completeness of implicit `auto` for what the fast path leaves open.
