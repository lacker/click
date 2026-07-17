# Click Language

Click files are sidecar specifications for C0 sources.

Terminology:

- **Surface Click** is the user-written `.click` language described here.
- **C fragments** are pieces of C0 syntax inside Surface Click, such as
  `p[k]`, `x + 1`, and `result == n`.
- **Kernel Click** is the explicit proof core produced by elaboration. Users
  normally do not write it directly.

## File Shape

```click
verifying "file.c";

int32 function_name(int32 p[], int32 n) {
    requires n >= 0;
    requires loadable(p[0..n]);
    ensures label: result == n by auto;
}
```

`verifying "file.c";` names a C source supplied to the verifier. Function
signatures in the `.click` file are checked against the parsed C0 source.

Click signatures currently understand `int32`, `uint8`, `int32*`, `uint8*`,
pilot `struct name*` parameters, and array-parameter spellings such as
`int32 p[]` and `uint8 bytes[]`.
Character literals such as `'x'`, `'\n'`, and `'\0'` are `uint8` values.

Inside C fragments and pure Click expressions over C values, `uint8` rvalues
promote to `int32` for arithmetic, ordered comparisons, shifts, and bitwise
operators. Assigning or returning an `int32` into `uint8` is checked narrowing:
the current pure facts must prove `0 <= value <= 255`.

Each `ensures` clause is a separate guarantee. A guarantee may be labeled with
`label:`. Omitting a proof clause uses the default prover, currently `auto`.

A function with several effect and postcondition clauses may instead use one
grouped execution proof after the contract block:

```click
int32 set_first(int32 p[], int32 value) {
    consumes p[0..1];
    mutable p[0..1];
    produces p[0..1];
    ensures result == value;
    ensures p[0] == value;
} by {
    execute_rest();
    frame();
    simp();
}
```

The trailing block executes the function once and proves every listed claim
from that shared replay. `frame()` discharges the effect claims, while
`simp()` and resource steps discharge the postconditions. A function uses
either this grouped form or per-claim `by` clauses; the two forms cannot be
mixed. Structural region clauses, including loop proofs, retain their own
proof blocks.

For contracts that need only ordinary execution, loop checks, framing, and
simplification, the grouped proof can be written `} by auto;`. This is a fixed
expansion of those steps. It does not search through composite-resource folds
or theorem applications; use an explicit grouped block for those operations.

Goal-specific pure reasoning can be isolated with `have`, including after the
function reaches its return frontier:

```click
execute_rest();
have exists (int32 k) { k == result } by {
    witness(k = result);
    simp();
}
simp();
```

The scoped proof may use `choose` and `witness`. Its established proposition is
added to every completed execution path, so later `simp()` can use it to close
the matching postcondition without applying those existential steps to other
contract claims.

Post-execution grouped steps run in source order. `fold`, `apply`, and `have`
update each symbolic path once; `frame()` closes its effect claims and `simp()`
closes the postconditions currently provable. Facts established after a closing
step do not retroactively affect it. All certificates for one symbolic path use
the same finalized specification.

## Pure Theorems

Pure theorem declarations prove Click propositions without attaching the proof
to a C function:

```click
theorem increment_preserves_positive(x: int32) {
    requires x >= 0;
    requires x < 2147483647;

    ensures x + 1 > 0 by auto;
}
```

Theorem parameters use `name: type` spelling. A theorem body uses the same
contract-block shape as C function specs: immutable `let` bindings,
proposition `requires` clauses, and proposition `ensures` clauses with proof
clauses. A theorem-only `.click` file does not need a `verifying "file.c";`
declaration.

Theorems are intentionally pure. They do not support resource `requires`,
resource `ensures`, effects, region proof blocks, `old(...)`, `at(...)`, or
`result`. Pure theorem proof scripts currently support `unfold(name);`,
`apply(theorem(args));`, and `simp();`; C execution and resource proof steps are
rejected. Applying a theorem never consumes, creates, returns, opens, or closes
resources.

Theorems can be reused by explicit application:

```click
theorem nonnegative_body(x: int32) {
    requires nonnegative(x);
    ensures x >= 0 by {
        unfold(nonnegative);
        simp();
    }
}

theorem reuses_nonnegative_body(y: int32) {
    requires nonnegative(y);
    ensures y >= 0 by {
        apply(nonnegative_body(y));
        simp();
    }
}
```

Proof-level `if` performs explicit case analysis on a pure proposition. It
checks the same current claim under the proposition and its negation:

```click
theorem int32_sign_split(x: int32) {
    ensures x <= 0 or x > 0 by {
        if x <= 0 {
            simp();
        } else {
            simp();
        }
    }
}
```

The same construct can appear before or after C execution in a function proof.
It splits proof reasoning only; it does not itself execute a C `if` statement.
Inside those proof cases, `execute_then_step()` and `execute_else_step()`
explicitly enter a selected arm of the next C `if`. Each step proves the
corresponding truth value of the C condition from current pure facts and moves
the execution point to the start of the arm without executing its body.

When both proof cases should continue through common code, `advance` gives the
branch-local execution a shared, explicit postcondition:

```click
advance(statement(1).exit)
ensuring {
    fact y >= 0;
}
by {
    if x >= 0 {
        execute_then_step();
        execute_step();
    } else {
        execute_else_step();
        execute_step();
    }
}
execute_step();
```

Each case must reach exactly the requested statement entry or exit and prove
every listed pure or resource fact. Click forgets facts, resources, scalar
values, mutable memory, and snapshots not named by that interface, then checks
the remaining proof from the resulting abstract frontier. Unchanged function
parameters and the function-entry state used by `old(...)` retain their stable
identity.

Statement IDs are global within a function and follow source preorder. An
`if` or loop receives its ID before statements nested in its arms or body; a
sequence does not receive a separate ID. The same IDs name execution targets,
annotations, and `at(statement(N).entry|exit, ...)` snapshots.

A structural clause may give a statement or loop a stable name with
`for statement(N) as label` or `for loop(N) as label`. Prefer that label in
proof scripts: `execute_until(label)`, `advance(label.exit)`, and
`at(label.entry, expression)` all resolve to the same code region.

`apply(...)` instantiates a verified theorem, proves that theorem's proposition
`requires` clauses from the current proof context, and adds its proposition
`ensures` clauses as derived facts. It does not change the current resource
context. Theorem declarations are checked in source order after the standard
library, so a theorem proof can apply stdlib theorems and earlier theorem
declarations. C function proof scripts can apply any verified theorem from the
standard library or the current file. Before function exit, `apply(...)`
immediately adds its conclusions to the current pure facts, so they can justify
the next `execute_step()`. After function exit it is checked separately on each
path, where `result`, post-state expressions, and ordinary `old(...)` arguments
can be evaluated.

## Requirements

Requirements are shared by all guarantees for the function.

Supported structural requirements:

```click
requires input_nonnegative: n >= 0;
requires loadable(p, 12);
requires loadable(p[0..n]);
requires loadable((p + 1)[0..1]);
requires loadable(p[0..n]);
requires separate(memory(dst[0..n]), memory(src[0..n]));
views p[0..1];
consumes p[0..1];
```

Requirement labels use the same `label:` spelling as `ensures` labels. Labels
are optional, but they are the preferred way for proof-step scripts to refer to a
specific precondition, for example `choose(k from requirement has_k);`.

`loadable(base[start..end])` and `memory(base[start..end])` use half-open
`int32` element ranges. The byte count is derived from the base pointer's
element type: four bytes for `int32[]`, one byte for `uint8[]`. This `..`
syntax is Click contract syntax, not C fragment syntax.

`loadable(base[start..end])` is the proposition form of memory loadability
for a segment. Use it when the fact needs to appear where Click expects a
proposition, such as a composite resource `fact`.

`requires` can also use Click propositions, but direct memory reads in
requirements are intentionally limited. If a precondition needs memory reads,
package it as a named predicate and unfold it at proof sites when needed.

## Read And Write Resources

Memory resources have viewed and owned resource elements. `views
base[start..end]` supplies persistent read access; `owns`, `consumes`, and
`produces` supply write access with the transfer behavior described below.
These are resource facts, not classical predicates, and are carried in the
verifier's resource context rather than copied as pure facts.

```click
int32 write_next(int32 p[], int32 x) {
    consumes p[0..1];
    requires x < 2147483647;

    ensures p[0] == x + 1 by auto;
    produces p[0..1] by auto;
}
```

Permission checking is mandatory for external memory. External loads require a
covering viewed or owned memory resource, and external stores require a covering
owned memory resource. Resource ranges use the element width of the pointer expression,
so `int32 p[]` ranges count four-byte cells and `uint8 bytes[]` ranges count
bytes. Local stack accesses do not require resources. A function with no
resource context has no permission to access external memory.
Top-level verification gets its resource context from the function's resource
verbs, while function calls apply the callee's verified contract as one opaque
execution step.

These permissions are currently one built-in resource family: memory resources.
The family defines how resources entail, split, rejoin, transfer, and consume
each other. This keeps the user-facing memory syntax concrete while sharing the
same context machinery with non-memory resources.

Click also supports exact-match token resources:

```click
resource open_fd(fd: int32);
```

After declaration, `owns open_fd(fd)`, `views open_fd(fd)`, `consumes
open_fd(fd)`, and `produces open_fd(fd)` use the same resource context. Token
resource arguments are type checked, and duplicate identical owned resource
elements in one resource context are rejected.

Composite resources are declared resources with a body:

```click
resource socket_open(fd: int32);

resource uncalled(flag: int32*) {
    contains socket_open(7);
    owns flag[0..1];
    fact flag[0] == 0;
}
```

Holding the folded abstract token exposes its immediate pure facts and viewed
resource facts, but not its owned contained permissions. Hidden contained
owned resources also expose direct `contains(...)` and `separate(...)` pure
facts. In an explicit proof script,
`observe(uncalled(flag));` non-destructively records this projection while
keeping owned permissions hidden. `unfold(uncalled(flag));` consumes the
abstract token resource fact and exposes its contained resource facts for
mutation. Composite bodies can bundle built-in memory resources and other
declared resources. Declared `fact` clauses are pure facts.
`fold(uncalled(flag));` proves the pure facts in the current state, consumes
the contained resource facts, and returns the abstract token resource fact. The
end of the `by { ... }` block checks the overall claim.

A function block may be resource-only when it consumes a resource:

```click
int32 complete(int32 cb) {
    consumes can_complete(cb);
}
```

Resource facts are written with resource verbs:

```click
int32 update(int32* p) {
    owns p[0..1];
}

int32 inspect(int32* p) {
    views p[0..1];
}

int32 close(int32 fd) {
    consumes open_fd(fd);
}

int32 open(int32 fd) {
    produces open_fd(fd);
}
```

`owns` means the function starts and ends with the owned resource. `views`
means the function can rely on the viewed/core resource without consuming it.
`consumes` requires an owned resource and does not return it. `produces`
returns an owned resource. `requires` and `ensures` accept pure propositions
only.

An owned memory resource implies its viewed core: ownership permits both loads
and stores, while a view permits loads and is copyable across calls. A callee
using `views` does not consume the caller's viewed or owned element. Owned
elements are transferred by `owns`, `consumes`, and `produces`. Allocation
lifecycle and deallocation authority are intentionally outside this first-layer
resource surface.

A call can pass a covered subrange, such as consuming `p[0..1]` from a caller
that owns `p[0..2]`; Click keeps the residue and rejoins adjacent returned
ranges. The same applies to symbolic ranges when the current facts prove the
subrange is covered. Viewed and owned memory elements also make the covered
range loadable for symbolic execution, so ordinary external reads and writes
do not need a separate `loadable(...)` requirement for the same range.

This is intentionally not the full permission system. There are no fractions,
ownership predicates, explicit resource algebra proof steps, C heap allocation,
or allocation-sized deallocation semantics yet. `loadable`, `mutable`, and
`immutable` remain separate concepts from permission: loadability proves an
access is in bounds, while resources authorize the access.

## Propositions

Click proposition connectives are words:

```click
result == x and not (result != x)
result == x implies result >= 0
forall (int32 k) { 0 <= k and k < n implies p[k] == old(p[k]) }
exists (int32 k) { 0 <= k and k < n and p[k] == x }
```

Do not use C logical operators such as `&&`, `||`, or `!` in Click
propositions. Those remain C-fragment syntax.

Range proposition helpers:

```click
(lo..hi).all(|k| { p[k] <= x })
(0..3).any(|k| { p[k] == x })
```

`.all` lowers to a guarded bounded universal proposition. `.any` lowers to a
bounded existential proposition when its bounds are symbolic; concrete `.any`
ranges still unroll to a finite disjunction. While lowering the range body, the
elaborator assumes the item is inside the range, so bodies such as `p[k] == x`
can use `loadable(p[lo..hi])` for memory safety.

Prefer these range combinators for guarded memory reads. A plain proposition
such as `exists (int32 k) { lo <= k and k < hi and p[k] == x }` does not
currently let the earlier conjunct guard the later memory read during lowering.

Existential goals are proved explicitly in proof-step scripts with `witness`.
The witness name must match the existential binder. For a symbolic `.any`, the
range item name is the existential binder:

```click
ensures found: (lo..hi).any(|k| { p[k] == result }) by {
    execute_rest();
    witness(k = lo);
    simp();
}
```

## `old(...)`

`old(expression)` evaluates a contract expression in the function-entry state.
It is mainly used in postconditions and invariants:

```click
ensures p[0] == old(p[0]) by auto;
ensures forall (int32 k) { 0 <= k and k < n implies p[k] == old(p[k]) } by auto;
```

Inside `old(...)`, `result` is unavailable.

When `old(p)` is passed as an array argument to a pure Click function or
predicate, it becomes an entry-state Click array ref. For example,
`permutation(p, old(p), 0, 2)` compares post-state `p` to entry-state `p`.
See [click-core.md](click-core.md).

## `at(...)`

`at(selector, expression)` evaluates a contract expression at a selected visit
to a program point. The initial supported selectors are deliberately narrow:

```click
at(function.entry, x)
at(loop_label.entry, x)
at(statement(0).entry, x)
at(statement(0).exit, x)
```

`at(function.entry, expression)` is equivalent to `old(expression)`.

The selected snapshot is a complete recorded C state, not only a memory
snapshot. Inside `at(...)`, reassigned parameters and declared scalar, pointer,
and array locals resolve to their values at that point. Outside `at(...)`,
function parameter names retain their ordinary contract meaning.

`at(loop_label.entry, expression)` is currently supported inside invariants for
that same labeled loop code region. It evaluates `expression` at the visit just
before the loop region starts, then reuses that snapshot for invariant entry and
preservation checks. Inside an explicit `preserve` proof, the same spelling is
scoped to the fresh arbitrary loop-head visit whose body iteration is being
proved.

`at(statement(N).entry, expression)` and
`at(statement(N).exit, expression)` are currently supported in proof-step
claims after deterministic execution records that statement point.
`execute_step()`, `execute_until(...)`, and `execute_rest()` all record every
deterministic statement boundary they cross. Executing an annotated loop uses
its verified abstract rule and records both `at(loop_label.entry, expression)`
and the unique post-loop state `at(loop_label.exit, expression)`. Branches still
require explicit arm selection and joining before a unique exit snapshot exists.
`advance(loop_label.exit)` can use that exit as a checked abstract interface for
the proof that follows.

`execute_until(statement(N))` starts at the current execution point, so it can
follow earlier `execute_step`, explicit branch-entry, or `advance` steps. The
target must be forward and reachable on that selected path; it cannot be used
to rewind execution or enter an unselected branch.

## Pure Click Functions

Click functions are specification-level value definitions, not executable C
functions.

```click
function inc(int32 x) -> int32 {
    x + 1
}

function eq_as_int(int32 x, int32 y) -> int32 {
    if x == y { 1 } else { 0 }
}

function count3(int32 p[], int32 x) -> int32 {
    let initial: int32 = 0;
    (0..3).fold(initial, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

Supported expression features include parameters, literals, `+`, `-`, `*`,
`/`, `%`, `<<`, `>>`, `int32` bitwise `&`, `|`, `^`, unary `~`, indexing,
`let name [: type] = value; body`, `if proposition { then } else { else }`,
range `.fold`, and calls to other non-recursive Click functions. Recursive
Click functions are rejected.

Function contracts may also use contract-level `let` bindings:

```click
int32 bounded_increment(int32 x) {
    let max: int32 = 2147483647;
    let expected = x + 1;

    requires x < max;
    ensures result == expected by auto;
}
```

Contract-level lets are immutable lexical abbreviations. They are visible to
later clauses in the same function block, including `requires`, `ensures`,
`mutable`, and region proof blocks. A contract-level let cannot reuse a C
parameter name or an earlier contract-level let name. Explicit type annotations
are checked when the binding is evaluated.

Use `old(...)` in the binding when the abbreviation must capture an entry-state
value. For example, `let data = old(owner->data);` gives later postconditions a
stable backing pointer even if the current `owner` metadata changes.

Proposition clauses may also use witness lets:

```click
let k: int32 where k == x;

ensures result == k by {
    execute_rest();
    witness(k = x);
    simp();
}
```

`let name: type where proposition; body` means `exists (type name) {
proposition and body }`. Contract-level `let ... where` applies that shape to
each later proposition clause. The type annotation is required. The current
implementation supports this in proposition clauses; it is intentionally
rejected in `loadable`, `mutable`, and other memory-segment expressions
until Click has a contract-wide witness environment.

In pure Click function parameters, `int32 p[]` and `int32* p` are treated as
array-ref parameters. `uint8 p[]` and `uint8* p` are also array-ref parameters,
with one-byte indexing and `uint8` loads. Indexing `p[k]` loads from the memory
snapshot carried by that argument. This is why `count(p, ...)` can be called
with either current `p` or `old(p)`.

Click array refs carry their element type. Passing an `int32[]` ref to a pure
Click function or predicate parameter declared as `uint8[]` is rejected.
The same typed array-ref model is used by loop-invariant spec lowering, so a
pure helper over `uint8[]` can appear in an invariant or inside `old(...)`.

The prelude currently provides byte-slice helpers over `uint8[]`: `byte_count`,
`bytes_equal`, `bytes_equal_range`, `bytes_all_eq`, `bytes_contains`, and
`bytes_all_not_eq`. It also provides first-pass C-string predicates:
`cstr_prefix`, `cstr_len`, `cstr`, and `cstr_bounded`. These are ordinary Click
functions and predicates, not built-in kernel concepts.

C0 accepts a small multi-field struct slice with `int32` and pointer-valued
fields. The C side can lower `obj->field` loads and stores at compact field
offsets. Click contracts can use field places in resources:
`views obj->field` and `owns obj->field`. The access resource also makes the
field loadable for symbolic execution. Explicit ranges such as
`owns owner[0..3]` are still available for broader footprints. A pointer
field occupies two int32 cells in that range spelling.

Concrete folds are unrolled. Symbolic folds remain `RangeFold` value terms in
the kernel and can be reasoned about by supported fold laws.

## Predicates

Predicates return Click propositions:

```click
predicate sorted_range(int32 p[], int32 lo, int32 hi) {
    forall (int32 i) {
        forall (int32 j) {
            lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}
```

Predicate calls are opaque by default. Requirements and loop invariants can
reuse exact predicate facts, but Click does not unfold predicate bodies unless a
proof asks for it:

```click
ensures sorted: sorted_range(p, 0, n) by {
    execute_rest();
    unfold(sorted_range);
    simp();
}
```

Loop invariants are declarations. Predicate bodies needed by the loop rule can
be exposed in its `initialize` and `preserve` proofs:

```click
for loop(0) {
    invariant sorted(p, n);
    initialize by {
        unfold(sorted);
        simp();
    }
    preserve by {
        unfold(sorted);
        simp();
    }
}
```

Either phase may be omitted, in which case Click uses `auto` for that phase.

Like pure Click functions, predicate array parameters are Click array refs.
A predicate can compare two arrays from different memory states when its caller
passes arguments such as `p` and `old(p)`.

Statement execution deterministically frames memory-dependent predicate facts
when it can prove the framed instance. Click substitutes the statement's
post-state memory into the predicate's array-ref arguments, unfolds the known
instance once, and checks that every explicit memory load in its body is
unchanged by the statement's certified exact writes. A store separate from
every cell used by the predicate therefore preserves the predicate
automatically; an overlapping store does not. This is bounded theorem
application, not heuristic predicate search or recursive unfolding.

## Effects

Function-level effects are separate from postconditions:

```click
immutable by frame;
mutable p[0..n] by frame;
mutable dst[0..n], counter[0..1] by frame;
```

`immutable` proves there are no externally visible memory writes. `mutable`
states an upper bound on externally visible writes. It does not claim every
listed cell changes. Function-level segment expressions are evaluated at
function entry, so a shifted segment such as `(owner->data + owner->len)[0..2]`
continues to denote the old two-cell tail after `owner->len` changes. Footprint
matching uses proven pointer equalities, including unchanged field loads across
a finite chain of certified memory effects.

Loop-level and step-level effects are described in [proof-workflow.md](proof-workflow.md)
and [memory-model.md](memory-model.md).
