# Click Language

Click files are sidecar specifications for C0 sources.

Terminology:

- **Surface Click** is the user-written `.click` language described here.
- **C fragments** are pieces of C0 syntax inside Surface Click, such as
  `p[k]`, `x + 1`, and `result == n`.
- **Kernel Click** is the internal, typed proof core produced by elaboration.
  It has no `.click` concrete syntax and is never emitted as proof text.

Surface Click is closed under expansion: every expression printed by
`click-expand`, the profiler, or a diagnostic is ordinary documented `.click`
syntax accepted by the same parser. Generated text is not a private dialect.

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
Those attached signatures deliberately retain C declaration order. Typed
binders introduced by Click itself use `name: type`: theorem and resource
parameters, pure-function and predicate parameters, typed `let` bindings, and
`forall`/`exists` variables.

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

An `ensures` clause describes every return state; it does not assert that a
return state exists. C contracts are partial-correctness contracts by default.
Checked undefined behavior, resource authority, and declared write footprints
remain safety properties of every finite execution prefix, including prefixes
of an execution that never returns.

C functions may call themselves or participate in mutual recursion without a
special Click keyword. Their ordinary contracts are the modular interfaces for
recursive calls. Click checks all functions in the selected call-graph
transaction before returning any verified rules, so declaration order does not
control whether a callee contract is available. This remains partial
correctness: `ensures` applies if a recursive call returns and the contract by
itself is not a termination proof. Recursive pure Click functions follow a
different rule: because a pure call must produce a value, every recursive
component requires a checked `decreases` measure.

### Optional C termination

Use `decreases` only when a caller needs separate evidence that a C function
returns. A function-level measure ranks recursive calls:

```click
int32 countdown(int32 n) {
    decreases n;
    ensures result == 0;
}
```

A loop measure belongs to that loop's region:

```click
for loop(0) {
    decreases n;
    invariant n >= 0;
}
```

Recursive traversal of an inductive resource may instead use its hidden
structural rank:

```click
int32 list_destroy(struct node* node) {
    decreases resource list(node);
    consumes list(node);
    ensures result == 0;
}
```

The declaration must exactly name an owned or viewed entry resource. The
current structural slice supports direct recursion, a guarded directly
recursive composite definition, and a simple resource guard. Every recursive
call path must establish that guard, either from a function precondition or
ordinary C control flow, and must pass one of the definition's direct
`contains` children. Click follows ordinary C-local aliases but does not accept
pointer inequality, a same-named unrelated resource, or a newly folded
resource as ancestry evidence. Because the separately certified partial
contract checks the actual resource transfer at each call, the traversal may
consume or mutate resources; postorder recursive deallocation is supported.
This proves descent of the finite resource witness, not descent of a pointer
value.

The numeric proof shape is also deliberately small. A function measure must be
one `int32` variable. A recursive edge passes `measure - K`, and a loop back
edge updates `measure = measure - K`, for a positive constant `K`; the path
guard must make the resulting value nonnegative. Mutually recursive functions
all declare their corresponding numeric parameter. Structural measures do not
yet support mutual C recursion. Nested rankings, mixed numeric/structural
tuples, and compound expressions are rejected rather than guessed.

Supplying any C `decreases` clause asks Click to certify termination of the
whole function, so every reachable loop and recursive component must be ranked
and every callee must itself have termination evidence. The kernel records
that evidence separately from `CVerifiedFunctionRule`. Ordinary calls and
ordinary `ensures` continue to use partial correctness and do not silently
depend on it. A perpetual service loop should therefore have an invariant but
no `decreases` clause.

A function with several effect and postcondition clauses may instead use one
grouped execution proof after the contract block:

```click
int32 set_first(int32 p[], int32 value) {
    owns p[0..1];
    mutable p[0..1];
    ensures result == value;
    ensures p[0] == value;
} by {
    execute();
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
execute();
have exists (k: int32) { k == result } by {
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

Like every Click-native declaration, theorem parameters use `name: type`
spelling. A theorem body uses the same contract-block shape as C function
specs: immutable `let` bindings,
proposition `requires` clauses, and proposition `ensures` clauses with proof
clauses. A theorem-only `.click` file does not need a `verifying "file.c";`
declaration.

Theorems are intentionally pure. They do not support resource `requires`,
resource `ensures`, effects, region proof blocks, `old(...)`, `at(...)`, or
`result`. Pure theorem scripts can simplify, unfold predicates, apply
theorems, introduce logical structure, rewrite, use exact assumptions, and
derive atomic propositions. They cannot execute C or transform resources.
Applying a theorem never consumes, creates, returns, opens, or closes
resources. The exact inventory is in the
[proof tactics reference](proof-tactics.md).

Pure theorems can use explicit strong induction on an `int32` parameter:

```click
theorem countdown_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            simp();
        } else {
            apply(ih(n - 1));
            simp();
        }
    }
}
```

`induct` must be the first tactic and the current requirements must establish
that its parameter is nonnegative. `ih(m)` is available only in that proof and
requires `m` to be nonnegative and strictly smaller, plus all theorem
requirements after substituting `m` for the induction parameter. Other theorem
parameters remain fixed. This is a pure proposition rule, not C execution or
C termination evidence.

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
Inside a case, smart `step()` uses the exact case fact to enter the selected C
arm. Expansion prints the corresponding `step() using { ... }` certificate.

When one transition needs contextual pure facts, list them explicitly:

```click
step() using {
    x < 2147483647;
}
```

Only those listed pure facts are visible to that C transition. Other facts stay
in the proof context for later tactics.

At an annotated loop entry, smart `summarize(loop(N))` consumes the already
verified loop rule and reaches its abstract exit. Its simple certificate is
`summarize(loop(N)) using { ... }`. Ordinary `step()` instead evaluates the
loop condition and enters at most one iteration.

When both proof cases should continue through common code, `reach` gives the
branch-local execution a shared, explicit postcondition:

```click
reach(statement(1).exit)
ensuring {
    fact y >= 0;
}
by {
    if x >= 0 {
        step();
        step();
    } else {
        step();
        step();
    }
}
step();
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
proof scripts: `execute_until(label)`, `reach(label.exit)`, and
`at(label.entry, expression_or_proposition)` all resolve to the same code
region.

`apply(...)` instantiates a verified theorem, requires each proposition
`requires` clause as an exact current pure fact or a context-free tautology,
and adds its proposition `ensures` clauses as derived facts. It does not search
the context for an implication that would establish a missing premise, and it
does not change the current resource context. Theorem declarations are checked in source order after the standard
library, so a theorem proof can apply stdlib theorems and earlier theorem
declarations. C function proof scripts can apply any verified theorem from the
standard library or the current file. Before function exit, `apply(...)`
immediately adds its conclusions to the current pure facts, so they can justify
the next `step()`. After function exit it is checked separately on each
path, where `result`, post-state expressions, and ordinary `old(...)` arguments
can be evaluated.

## Requirements

Requirements are shared by all guarantees for the function.

Supported structural requirements:

```click
requires input_nonnegative: n >= 0;
requires loadable(p[0..n]);
requires loadable((p + 1)[0..1]);
requires separate(memory(dst[0..n]), memory(src[0..n]));
requires defined(x + 1);
views p[0..1];
consumes p[0..1];
```

Requirement labels use the same `label:` spelling as `ensures` labels. Labels
are optional, but they are the preferred way for proof scripts to refer to a
specific precondition, for example `choose(k from requirement has_k);`.

`loadable(base[start..end])` and `memory(base[start..end])` use half-open
`int32` element ranges. The byte count is derived from the base pointer's
element type: four bytes for `int32[]`, one byte for `uint8[]`. This `..`
syntax is Click contract syntax, not C fragment syntax.

`loadable(base[start..end])` is the proposition form of memory loadability
for a segment. Use it when the fact needs to appear where Click expects a
proposition, such as a composite resource `fact`.

`defined(expression)` is a pure proposition stating that evaluating the C0
expression reaches a value rather than undefined behavior. Click elaborates it
with the kernel's C expression semantics, so signed overflow, division, shifts,
and memory-load obligations share the same rules as execution. It currently
accepts C0 expression fragments; `old`, `at`, folds, lets, and Click function
calls inside `defined(...)` are not yet supported.

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
    owns p[0..1] by auto;
    requires x < 2147483647;

    ensures p[0] == x + 1 by auto;
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

A composite body may instead have one top-level guard:

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        contains list(node->next);
    }
}
```

There is no `else`: when the guard is false, the body is empty. The guard must
be load-free, because it decides which memory permissions exist and therefore
cannot depend on reading that same memory. A guarded body may directly contain
the resource being defined. This direct self-recursion is the supported
recursive form; unguarded recursion and mutual resource cycles are rejected.

`observe` keeps a guarded resource opaque when neither the guard nor its
negation is known. Explicit `fold` and `unfold` require the guard to be decided.
When active, they expose or consume exactly one body layer, leaving a recursive
child such as `list(node->next)` folded. This makes proof cost depend on the
number of explicit list operations, not the unknown length of the list.

Holding the folded abstract token exposes its immediate pure facts and viewed
resource facts, but not its owned contained permissions. Hidden contained
owned resources also expose direct `contains(...)` and `separate(...)` pure
facts. In an explicit proof script,
`observe(uncalled(flag));` non-destructively records this projection while
keeping owned permissions hidden. `unfold(uncalled(flag));` consumes the
abstract token resource fact and exposes its contained resource facts for
mutation. Composite bodies can bundle built-in memory resources and other
declared resources. Declared `fact` clauses are pure facts.
Before `fold(uncalled(flag));`, the declared pure body facts must be exact facts
in the current proof context (or normalize to true without context). `fold`
then consumes the contained resource facts and returns the abstract token
resource fact. It does not invoke `simp`; use an explicit `have` first when a
body fact needs derivation. The end of the `by { ... }` block checks the overall
claim.

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
only. Prefer `owns X by proof;` over the exactly equivalent pair
`consumes X;` and `produces X by proof;`; keep the separate verbs for one-way
transfers and resource transformations.

An owned memory resource implies its viewed core: ownership permits both loads
and stores, while a view permits loads and is copyable across calls. A callee
using `views` does not consume the caller's viewed or owned element. Owned
elements are transferred by `owns`, `consumes`, and `produces`.

Fixed-size heap objects add the built-in owned resource
`allocation(base, bytes)`. It is exclusive authority and responsibility for
one live heap lifetime; it does not authorize memory access. Complete access is
spelled separately with `object(base)`. Allocation authority cannot be
`views`-ed or duplicated, and a verified function may not silently drop it:
the authority must be returned (possibly inside a composite resource) or
consumed by an actual `free`.

```click
resource owned_item(item: struct item*) {
    if item != 0 {
        contains allocation(item, sizeof(struct item));
        owns object(item);
    }
}
```

The conditional body gives a nullable factory one uniform result resource.
On the null branch the body is empty. On the success branch it packages both
access and lifetime authority. A read-only helper can `views owned_item(item)`
without gaining the ability to free it; a destructor must consume and unfold
the owned wrapper before calling `free`.

When the guard is not known at function entry, a proof-level `if` can split on
it even if the C body is branchless. Each proof case unfolds the matching
resource body: the empty branch certifies operations such as `free(NULL)`, and
the active branch exposes the resources those operations consume. Exact
contract certification checks both cases independently, so this does not add
a precondition or require rewriting the C control flow.

Composite and token arguments are compared using proved scalar and pointer
equalities. Thus a held `list(node->next)` can satisfy `list(tail)` after the
proof establishes `node->next == tail`; the resource does not depend on one
particular syntactic spelling of that pointer.

A call can pass a covered subrange, such as consuming `p[0..1]` from a caller
that owns `p[0..2]`; Click keeps the residue and rejoins adjacent returned
ranges. The same applies to symbolic ranges when the current facts prove the
subrange is covered. Viewed and owned memory elements also make the covered
range loadable for symbolic execution, so ordinary external reads and writes
do not need a separate `loadable(...)` requirement for the same range.

This is intentionally not the full permission system. There are no fractions,
general ownership predicates, runtime-sized allocation, or user-defined
resource algebras. `loadable`, `mutable`, and `immutable` remain separate
concepts from permission: loadability proves an access is in bounds, while
resources authorize the access.

## Propositions

Click proposition connectives are words:

```click
result == x and not (result != x)
result == x implies result >= 0
forall (k: int32) { 0 <= k and k < n implies p[k] == old(p[k]) }
exists (k: int32) { 0 <= k and k < n and p[k] == x }
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
such as `exists (k: int32) { lo <= k and k < hi and p[k] == x }` does not
currently let the earlier conjunct guard the later memory read during lowering.

Existential goals are proved explicitly in proof scripts with `witness`.
The witness name must match the existential binder. For a symbolic `.any`, the
range item name is the existential binder:

```click
ensures found: (lo..hi).any(|k| { p[k] == result }) by {
    execute();
    witness(k = lo);
    simp();
}
```

## `old(...)`

`old(expression)` evaluates a contract expression in the function-entry state.
It is mainly used in postconditions and invariants:

```click
ensures p[0] == old(p[0]) by auto;
ensures forall (k: int32) { 0 <= k and k < n implies p[k] == old(p[k]) } by auto;
```

Inside `old(...)`, `result` is unavailable.

When `old(p)` is passed as an array argument to a pure Click function or
predicate, it becomes an entry-state Click array ref. For example,
`permutation(p, old(p), 0, 2)` compares post-state `p` to entry-state `p`.
See [click-core.md](click-core.md).

## `c(...)`

`c(name)` explicitly refers to the binding named `name` in the verified C
program. It is distinct from Click built-ins and contract bindings with the
same spelling. In particular, bare `result` is the function's contract result,
while `c(result)` is a C parameter or local named `result`.

C locals exist only while they are in scope. After function exit, refer to a
local through a recorded program point:

```click
result == at(statement(1).entry, c(result))
```

The AST retains this distinction; `c(result)` is not converted to an ordinary
string variable and cannot be reinterpreted as contract `result`. Expansion
uses this spelling when a generated certificate must name an overlapping C
binding.

## `at(...)`

`at(selector, expression)` evaluates a contract expression at a selected visit
to a program point. In a proposition position, `at(selector, proposition)`
evaluates the complete proposition at that visit:

```click
at(function.entry, x)
at(loop_label.entry, x)
at(statement(0).entry, x)
at(statement(0).exit, x)
at(statement(0).entry, p[0] == 7)
at(statement(0).entry, loadable(p[0..n]))
```

`at(function.entry, expression)` is equivalent to `old(expression)`. The
proposition form snapshots every state-relative part of the proposition
together. This matters for propositions such as `loadable(...)`: both the
address expression and the memory in which it is loadable come from the
selected state.

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

The expression and proposition forms of `at(statement(N).entry, ...)` and
`at(statement(N).exit, ...)` are currently supported in explicit proof-script
claims after deterministic execution records that statement point.
`step()`, `execute_until(...)`, and `execute()` all record every
deterministic statement boundary they cross. Executing an annotated loop uses
its verified abstract rule and records both `at(loop_label.entry, expression)`
and the unique post-loop state `at(loop_label.exit, expression)`. Branches still
require explicit arm selection and joining before a unique exit snapshot exists.
`reach(loop_label.exit)` can use that exit as a checked abstract interface for
the proof that follows.

`execute_until(statement(N))` starts at the current execution point, so it can
follow earlier `step`, explicit branch-entry, or `reach` steps. The
target must be forward and reachable on that selected path; it cannot be used
to rewind execution or enter an unselected branch.

## Pure Click Functions

Click functions are specification-level value definitions, not executable C
functions. Their parameters are Click-native binders and therefore use
`name: type`, unlike attached C function signatures.

```click
function inc(x: int32) -> int32 {
    x + 1
}

function eq_as_int(x: int32, y: int32) -> int32 {
    if x == y { 1 } else { 0 }
}

function count3(p: int32[], x: int32) -> int32 {
    let initial: int32 = 0;
    (0..3).fold(initial, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

Supported expression features include parameters, literals, `+`, `-`, `*`,
`/`, `%`, `<<`, `>>`, `int32` bitwise `&`, `|`, `^`, unary `~`, indexing,
`let name [: type] = value; body`, `if proposition { then } else { else }`,
range `.fold`, and calls to other Click functions.

Recursive pure functions must declare a well-founded natural-number measure:

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}
```

Every direct or mutual recursive edge must pass a nonnegative measure strictly
smaller than the caller's. The initial slice restricts the measure to one named
`int32` parameter and recursive components to `int32` parameters and results.
Concrete calls evaluate to a base case. Symbolic calls expose one equation and
leave the next recursive application opaque, so verification never guesses a
recursion depth. This total value semantics is intentionally different from
partial-correctness C recursion.

General properties of symbolic recursive calls use theorem-level
`induct(parameter) as hypothesis`. Induction is explicit and strong: applying
the local hypothesis checks a nonnegative strictly smaller argument and the
theorem's substituted requirements. `simp` does not invent induction, and a
pure function's `decreases` clause remains definition-totality evidence rather
than a theorem about the result.

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
    execute();
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

In pointer-valued C0 contexts, the integer constant `0` is the null pointer
constant. It may initialize or assign a pointer, be returned from a pointer
function, be passed to a pointer parameter, or be compared with a pointer.
Nonzero integers do not implicitly convert to pointers.

C0 accepts a small multi-field struct slice with `int32` and pointer-valued
fields. The C side lowers chained `obj->child->field` loads and stores at
LP64-aligned byte offsets while retaining intermediate struct-pointer types.
Click contracts can use field places in resources:
`views obj->field` and `owns obj->field`. The access resource also makes the
field loadable for symbolic execution.

Use `object(obj)` for the complete storage of a struct object:

```click
consumes object(owner);
fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
```

`object(owner)` is layout-aware: it denotes the imported C struct's aligned
size without exposing byte offsets or pretending that a pointer field is a
pair of source-level `int32` fields. Use `owner->field` for one field and
`object(owner)` for the complete object. Explicit ranges such as
`p[0..count]` remain the normal spelling for array storage.

Surface Click also has documented low-level memory reads for addresses that do
not have a recoverable C source place:

- `load_int32(pointer)` and `load_uint8(pointer)`
- `load_int32_pointer(pointer)` and `load_uint8_pointer(pointer)`
- `byte_offset(pointer, bytes)`

These are Surface Click escape hatches, not Kernel Click syntax. The canonical
renderer prefers `owner->field` whenever imported layout provenance identifies
the address. Expansion may emit a low-level read only when no source field
place is available.

Concrete folds are unrolled. Symbolic folds remain `RangeFold` value terms in
the kernel and can be reasoned about by supported fold laws.

## Predicates

Predicates return Click propositions:

```click
predicate sorted_range(p: int32[], lo: int32, hi: int32) {
    forall (i: int32) {
        forall (j: int32) {
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
    execute();
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
