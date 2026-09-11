# Click language reference

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

## File shape

<!-- verified-example: mdtests/argument_result.md -->
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

Click signatures currently understand `void` C return types, `int32`/`int`/
`int32_t`, `uint8`/`unsigned char`/`uint8_t`, and scalar `uint32`/
`unsigned int`/`uint32_t` forms, plus the existing pointer forms, pilot
`struct name*` parameters, and array-parameter spellings such as `int32 p[]`
and `uint8 bytes[]`. C typedefs may alias these modeled types. `uint32` is
currently scalar-only: pointers, arrays, and struct fields of that type remain
unsupported. `void` is not an object or parameter type. A `void` contract has
no `result` binding; it may still state resource transfer and return-state
propositions that do not mention a result.
Character literals such as `'x'`, `'\n'`, and `'\0'` are `uint8` values.

Inside C fragments and pure Click expressions over C values, `uint8` rvalues
promote to `int32` for arithmetic, ordered comparisons, shifts, and bitwise
operators, assignments, and returns. `uint32` addition, subtraction, and
multiplication wrap at 2^32; division and remainder use unsigned arithmetic,
bitwise operators use the raw 32-bit pattern, and right shifts are logical.
Equality compares the bit pattern and ordered comparisons use unsigned order.
Assigning
or returning an `int32` into `uint8` is checked narrowing: the current pure
facts must prove `0 <= value <= 255`.

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

<!-- verified-example: mdtests/c_decreases_recursive.md -->
```click
int32 countdown(int32 n) {
    decreases n;
    ensures result == 0;
}
```

A loop measure belongs to the loop handled at the current execution frontier:

<!-- verified-example: mdtests/c_decreases_loop.md -->
```click
by {
  loop {
    decreases n;
    invariant n >= 0;
  }
}
```

Recursive traversal of an inductive resource may instead use its hidden
structural rank:

<!-- verified-example: mdtests/c_decreases_resource_recursive.md -->
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
ordinary C control flow. Guard matching uses C meaning rather than one
spelling: negation, branch polarity, symmetric equality, and corresponding
ordered comparisons are normalized. The call must pass one of the definition's
direct `contains` children. Click follows ordinary C-local aliases but does not
accept pointer inequality, a same-named unrelated resource, or a newly folded
resource as ancestry evidence. Because the separately certified partial
contract checks the actual resource transfer at each call, the traversal may
consume or mutate resources; postorder recursive deallocation is supported.
This proves descent of the finite resource witness, not descent of a pointer
value.

The numeric proof shape is deliberately small but loop measures may be
arbitrary current int32 expressions or a nonempty lexicographic tuple of
expressions. A loop back edge must keep every component nonnegative and make
one component strictly smaller while keeping all earlier components equal. For
example, `decreases n - i` ranks a loop that increments `i` toward `n`.

A loop's ranking obligations are members of the back-edge invariant bundle,
not a separate kernel pass. When a loop declares `decreases`, the bundle its
`close_invariants` closer proves gains, after the invariants in declaration
order, one `0 <= component` obligation per declared component in declaration
order, then one decrease obligation. For a single component that obligation is
`post < pre`; for a tuple it is the disjunction over pivots, `post[0] < pre[0]`
or `post[0] == pre[0] and post[1] < pre[1]`, and so on, where `pre` reads the
component at the start of the iteration and `post` at the back edge. Choosing
the pivot is therefore an ordinary `left` or `right` arm choice that the proof
makes and [`click expand`](../cli/expand.md) prints, not a search the kernel
performs. `close_invariants()` plans those members with the same bounded
search it uses for the invariants; where it misses, spell them in a
`close_invariants by { ... }` body, whose `both { ... } and { ... }` structure
follows the member order above. An explicit closer body written before a
`decreases` clause existed fails promptly, and the diagnostic names the
ranking members the bundle now carries.

Arithmetic premises for those members are the cited ones only, so a member is
closed with `arithmetic() using { ... }` naming the guard, precondition, and
invariant facts it needs. The iteration's entry values are available as
`at(statement(N).entry, x)`, the same spelling loop-body premises use. The
smart closer cites from one named set: the loop's declared invariants, the
loop guard, and the function's written preconditions, each in whichever of
those two spellings holds where the member is proved. An inequality that is
in scope but is none of those is not a candidate, so a member that needs one
fails at that member instead of being closed by a search over ambient facts;
cite it by hand in a `close_invariants by { ... }` body, or declare it as an
invariant.
<!-- verified-example: mdtests/c_decreases_lexicographic_loop.md -->
```click
loop {
    decreases (outer, inner);
    invariant outer >= 0;
    invariant inner >= 0;
}
```
Function-level numeric measures remain one unchanged `int32` parameter, and a
recursive edge still passes `measure - K` for a positive constant `K`.
Mutually recursive functions all declare their corresponding numeric
parameter. Every variable mentioned by a numeric measure must also remain
unaddressed: if its address is taken anywhere (`&measure`), a store through
that pointer, directly or inside a callee, could change the measure without a
ranked update, so the plan is rejected. Structural measures do not yet support
mutual C recursion. Loop-local lexicographic tuples are supported; nested-loop
propagation treats a separately ranked inner loop as an opaque terminating
phase. If it writes a variable mentioned by the enclosing tuple, the kernel
forgets that variable's scalar alias and relies on the enclosing invariants for
the post-phase nonnegativity proof. Recursive calls inside loops remain
supported only when both obligations are proved independently: the loop needs
its own ranking, and every recursive edge still needs the function-level
measure. The loop guard is available when proving the recursive argument is
nonnegative. The numeric function-level measure must remain unchanged by
assignments, updates, allocation results, and call results. Structural
recursive calls in loops are supported for read-only resource transitions when
the parent is observed before the loop; the recursive call must still receive
a direct contained child. See
`mdtests/c_decreases_resource_recursive_in_loop.md`. Resource-consuming or
mutating structural calls across a loop back edge remain tracked in the
hard-bucket `issues/recursion.md`.
Recursive calls whose descent depends on a changing lexicographic caller
measure remain unsupported.

Supplying any C `decreases` clause asks Click to certify termination of the
whole function, so every reachable loop and recursive component must be ranked
and every callee must itself have termination evidence. The kernel records
that evidence separately from `CVerifiedFunctionRule`. Ordinary calls and
ordinary `ensures` continue to use partial correctness and do not silently
depend on it. A perpetual service loop should therefore have an invariant but
no `decreases` clause.

Termination and host capacity are separate judgments. Click does not model
process stack exhaustion, address-space exhaustion, operating-system
allocation failure, or local-storage limits. A verified function can still
run out of those host resources; the worker's stack size and verifier budgets
are not program guarantees. The perpetual-loop regressions in the [examples
reference](../examples.md) pin this partial-correctness boundary.

A function with several postcondition clauses may instead use one grouped
execution proof after the contract block:

<!-- verified-example: mdtests/grouped_function_proof.md -->
```click
int32 set_first(int32 p[], int32 value) {
    owns p[0..1];
    ensures result == value;
    ensures p[0] == value;
} by {
    execute();
    simp();
}
```

The trailing block executes the function once and proves every listed claim
from that shared execution. It may also certify a resource-only contract with
no postcondition clauses. `simp()` and resource steps discharge the
postconditions. A function uses either this grouped form or per-claim `by`
clauses; the two forms cannot be mixed. Structural region clauses, including
loop proofs, retain their own proof blocks.

For contracts that need only ordinary execution, loop checks, and
simplification, the grouped proof can be written `} by auto;`. This is a fixed
expansion of those steps. It does not search through composite-resource folds
or theorem applications; use an explicit grouped block for those operations.

Goal-specific pure reasoning can be isolated with `have`, including after the
function reaches its return frontier:

<!-- verified-example: mdtests/post_execution_have_checks_each_path.md -->
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
update each symbolic path once; `simp()` closes the postconditions currently
provable. Facts established after a closing
step do not retroactively affect it. All claim proofs for one symbolic path use
the same finalized specification.

Inside a proof-level `if`, post-execution tactics apply only to execution paths
compatible with that branch's checked condition. In particular, a closing step
does not plan operations for a contradictory sibling outcome and then align
them by vector position. Branch-local expansion therefore preserves the sibling's
proof text and reports a compact `pN` path identifier if surface and execution
coverage ever diverge.

## Mathematical integers

`Integer` is the specification type for signed mathematical integers of
arbitrary size. It is separate from the C type `int` (an alias for `int32`).
Integer addition, subtraction, negation, and multiplication are exact and do
not generate machine-overflow obligations.

Integer is supported in specification bindings, typed `let` bindings, theorem
and pure-function parameters and results, quantifiers, datatype fields and
generic arguments, resource fields and patterns, and typed range folds.
Applications support exact Integer guards, explicit `using` premises, and
mixed Integer/C parameters. Unsuffixed decimal literals take their type from
an Integer expression, including values larger than 64 bits.
Machine variables and suffixed machine literals require explicit conversions.
`to_integer(value)` preserves the numeric value of each supported machine
integer type: `int16`, `int32`, `uint8`, `uint16`, `uint32`, `int64`, and `uint64`.
Signed `-1` and unsigned `4294967295u32` therefore produce different Integers.
Evaluating the argument retains its C definedness obligations. For example,
`to_integer(x + 1)` requires established evidence of `defined(x + 1)`, even in
a reflexive comparison. This requirement survives aliases, nested arithmetic,
and conditional expressions; an overflowing C addition remains invalid.

The reverse names are `to_int16`, `to_int32`, `to_uint8`, `to_uint16`,
`to_uint32`, `to_int64`, and `to_uint64`. Exact constants must lie within the
destination's range. Symbolic values require established lower and upper bounds;
for example, `to_int32(z)` requires `z >= -2147483648` and `z <= 2147483647`.
Missing either bound rejects the conversion, including inside reflexive claims.
No conversion wraps, truncates, or implicitly mixes the two types.
See [conversion examples](https://github.com/lacker/click/blob/master/mdtests/integer_machine_conversions.md).

<!-- verified-example: mdtests/integer_successor.md -->
```click
theorem integer_successor(z: Integer) {
    ensures z + 1 > z by {
        simp();
    }
}
```

Equality, disequality, and the ordinary order comparisons are supported.
`simp()` can produce explicit arithmetic evidence for supported linear
comparisons. General multiplication is a valid expression; it does not imply
a general nonlinear arithmetic solver. Expanded proofs retain the arithmetic
evidence for ordinary verification to check.

Fold terms are checked opaque atoms in the supported linear certificate
fragment. An empty-range or append law supplies the fold step explicitly, and
the certificate retains the exact fold carrier, endpoints, body, and memory
snapshot identity. Alpha-equivalent loads from one retained snapshot may
match; a different snapshot or a changed endpoint, body, or carrier does not.
The bounded affine planner uses selected checked premises and explicit
constant coefficients. It does not enumerate a range or introduce an
unchecked arithmetic assumption.

Integer values have no C storage or runtime representation. Datatype fields and
generic arguments such as `Box<Integer>` are supported, as is extraction from
known constructors. Symbolic Integer-valued datatype matches are supported when
the matched result has one consistent carrier; contextual Integer literals in
their arms inherit that result type. Mixed C and Integer arithmetic remains
rejected unless an explicit conversion is present.
Resources may declare `field total: Integer;`: folding checks the resource's
facts, and `old(model.total)` retains the entry value across updates.
Checked resource pattern bindings retain each field's declared carrier, name,
entry/current snapshot, and definedness while the pattern is lowered and
rechecked. See [resource field examples](https://github.com/lacker/click/blob/master/mdtests/integer_resource_fields.md).

Pure functions with Integer parameters and results are supported. Calls remain
opaque until an explicit `unfold(function(args))` exposes the defining equation.
Arithmetic may treat an opaque result as an unknown Integer without unfolding.
A smart tactic may emit a checked unfold step; expansion makes that step visible.
See [the function example](https://github.com/lacker/click/blob/master/mdtests/integer_function_successor.md).

Integer and mixed C/Integer quantifiers support checked introduction and
instantiation over their logical, unbounded domains. Integer range folds support
typed scalar bodies and checked empty and append laws for `Int32` and `Integer`;
expansion preserves those checked applications. Array- and memory-reading fold
bodies use scoped definedness and exact snapshot identity. Integer existential
witnesses may contain indexed reads when their loadability and conversion
obligations are checked. A complete C loop proof still needs its own prefix,
intermediate definedness, and loop-invariant obligations; range folds do not
enumerate a symbolic array to discharge those obligations.
Checked conversions between `Nat` and `Integer` are available; implicit
conversions to C integers are not.
Division and remainder are deferred; when implemented they will use Euclidean
semantics. Bitwise operators remain unavailable for `Integer` values. See the
[mathematical Integer internals](../../internals/mathematical-integers.md) for
the supported coverage, definedness rules, and deferred work. `Nat` remains the
existing [structural natural-number datatype](../library/index.md#natural-numbers).

## Pure theorems

Pure theorem declarations prove Click propositions without attaching the proof
to a C function:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
theorem increment_preserves_positive(x: int32) {
    requires x >= 0;
    requires x < 2147483647;

    ensures x + 1 > 0 by auto;
}
```

Like every Click-native declaration, theorem parameters use `name: type`
spelling. A symbolic callback uses a nameless C function-pointer declarator
as its type, for example `step: void (*)(int32*)`; the bound value remains an
ordinary function pointer, and behavioral knowledge remains an explicit
`Contract(step)` proposition. A theorem body uses the same contract-block shape as C function
specs: immutable `let` bindings,
proposition `requires` clauses, and proposition `ensures` clauses with proof
clauses. A theorem-only `.click` file does not need a `verifying "file.c";`
declaration.

Theorems are intentionally pure. They do not support resource `requires`,
resource `ensures`, region proof blocks, `old(...)`, `at(...)`, or
`result`. Pure theorem scripts can simplify, unfold predicates and pure functions, apply
theorems, introduce logical structure, rewrite, use exact assumptions, and
derive atomic propositions. They cannot execute C or transform resources.
Applying a theorem never consumes, creates, returns, opens, or closes
resources. The exact inventory is in the
[proof tactics reference](../tactics/index.md).

Pure theorems can use explicit strong induction on an `int32` parameter:

<!-- verified-example: mdtests/pure_induction_countdown.md -->
```click
theorem countdown_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(countdown(n));
            normalize() using { n <= 0; }
        } else {
            apply(ih(n - 1));
            unfold(countdown(n));
            rewrite(countdown(n - 1) == 0);
            normalize();
        }
    }
}
```

`induct` must be the first tactic and the current requirements must establish
that its parameter is nonnegative. `ih(m)` is available only in that proof and
requires `m` to be nonnegative and strictly smaller, plus all theorem
requirements after substituting `m` for the induction parameter. Other theorem
parameters remain fixed. This is a pure proposition rule, not C execution or
C termination evidence. Bare `apply(ih(m))` is smart: expansion proves those
fixed obligations and emits `apply(ih(m)) using { ... }`. The `using` form is
the simple checked operation and accepts only the exact listed obligations.

Pure-function calls can be opened explicitly with
`unfold(function(args))`. This simple operation exposes one defining equation
at the current proof state. It never recursively expands the resulting call
tree; a recursive call in the selected body remains opaque until a later
explicit unfold. Lowering never executes a pure Click function, even when all
of its arguments are concrete: the application remains a typed logical term
until such an unfold step is requested. Likewise, `match` over an unknown
algebraic value remains one symbolic match term; it does not split C execution
paths. A match reduces directly only when its scrutinee is already a checked
constructor.

Theorems can be reused by explicit application:

<!-- verified-example: mdtests/pure_theorem_apply.md -->
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

<!-- verified-example: mdtests/proof_if_cases.md -->
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
Inside a case, `step()` uses the case fact to enter the selected C arm.

When a C `if` is at the execution frontier, use `branch` instead of repeating
its condition as a logical case split:

<!-- verified-example: mdtests/frontier_branch.md -->
```click
branch {
    then {
        step();
    }
    else {
        step();
    }
}
step();
```

`branch` reads the guard from the C source and enters every feasible arm. Each
nonreturning arm must stop at the C `if`'s shared continuation, after which the
following proof continues once from one joined state. An arm that returns
closes its own outcome inside the arm; it does not run the continuation after
`branch`. The tactic fails if the current frontier is not a C `if`.

A transition sees every fact in the proof context. When a statement's
prerequisite is not yet available, establish it with `have` before the step:

<!-- verified-example: mdtests/simple_statement_step_requires_exact_prerequisite.md -->
```click
step();
```

At a loop entry, `loop { ... }` verifies initialization and one arbitrary
iteration, constructs the kernel loop rule, applies it, and reaches the
abstract exit. It fails if the current frontier is not a loop. Ordinary
`step()` instead evaluates the loop condition and enters at most one concrete
iteration; it does not invent a loop summary.

When the two arms need to expose facts or resources about changed state, add an
optional common-frontier interface to `branch`:

<!-- verified-example: mdtests/proof_branch_interface_continuation.md -->
```click
branch {
    ensuring {
        fact y >= 0;
    }
    then {
        step();
    }
    else {
        step();
    }
}
step();
```

Every continuing arm must prove every listed pure or resource fact. The
interface augments the deterministic common state; it is not an exhaustive
whitelist, so exact common facts and resources remain available without being
restated. Arm-only information is forgotten. If plain `branch` cannot form a
useful deterministic join, Click asks for an `ensuring` block rather than
retaining hidden path states or searching for an interface.

Statement IDs are global within a function and follow source preorder. An
`if` or loop receives its ID before statements nested in its arms or body; a
sequence does not receive a separate ID. The same IDs name execution targets,
annotations, and `at(statement(N).entry|exit, ...)` snapshots.

A frontier-local loop tactic may give the loop it encounters a stable name
with `loop as label { ... }`.  The label names that encountered loop's entry
and exit snapshots; it never searches for or jumps to a source region.  Use
`at(label.entry, expression_or_proposition)` and
`at(label.exit, expression_or_proposition)` after the tactic has established
those points. Intermediate propositions are proved with `have` in the ordinary
forward proof, so they use the resources, premises, and execution frontier
established by the preceding tactics rather than starting a separate traversal
from function entry.

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

## Callback execution theorems

An ordinary theorem has no execution frontier. An explicit `executes` clause
instead proves a contract implication by checking one arbitrary callback call:

<!-- verified-example: mdtests/c_contract_executes_buffer.md -->
```click
resource Buffer(data: int32*, count: int32) {
    owns data[0..count];
}
contract void Raw(int32* data, int32 count) {
    requires count >= 0;
    owns data[0..count];
}
contract void Buffered(int32* data, int32 count) {
    requires count >= 0;
    owns Buffer(data, count);
}
theorem raw_is_buffered(callback: void (*)(int32*, int32))
    executes callback(int32* data, int32 count)
{
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data, count));
        step(Raw);
        fold(Buffer(data, count));
        simp();
    }
}
```

The proof starts with arbitrary call arguments and the **target contract's**
input requirements and resources. It knows only the callback contracts in the
theorem's premises or established by checked proof steps—not the target
contract fact being proved. The call checks the selected source contract's
requirements and performs its resource transition. The remaining proof must
establish all target postconditions, returned resources, and write bounds. Unrelated owned resources use ordinary framing.

These are ordinary execution proof blocks: `have`, theorem application,
rewriting, proof cases, `fold`, `unfold`, and the usual closing tactics retain
their normal meanings. Every feasible proof case must execute the call. The
checked result is a reusable contract implication: `apply(raw_is_buffered(f))`
establishes `Buffered(f)`, after which an ordinary caller can use
`step(Buffered)`. Expansion preserves the explicit contract selection.

Return-valued callbacks use the same syntax: the theorem parameter's C
function-pointer type supplies the return type. `step(Contract)` performs the
call and forwards its actual return value to `result` in one checked step.
The proof may relate `result` to current or `old` memory and to guarantees
from other applicable contracts. There is no extra proof step to expose the
result, and no new result-binding syntax. Existing supported scalar and pointer
return types retain their C types. See the
[end-to-end return-valued buffer proof](https://github.com/lacker/click/blob/master/mdtests/c_contract_executes_return_buffer.md).

An explicit proof `if` after `step(Contract)` may distinguish success and
failure using `result`. Conditional postconditions remain conditional until
their guard is established; `extract` exposes the selected consequence.
Each case must return the target resources, and failure does not inherit
success's update guarantee (nor success failure's preservation guarantee).
The [status-returning callback tests](https://github.com/lacker/click/blob/master/mdtests/c_contract_executes_status.md)
cover this refinement and an ordinary C caller that checks the returned status.
These proof cases may nest: each inner arm receives its own condition, and
the continuation after an inner `if` must check in every reachable case.
See the [nested status cases](https://github.com/lacker/click/blob/master/mdtests/c_contract_executes_status_nested.md),
including an impossible arm and a shared continuation containing another case.

This slice supports one nongeneric callback theorem parameter,
one target-contract conclusion, and one or more source-contract premises for
that same pointer. The `executes` arguments use C parameter spelling, match
the callback signature, and are bound only inside the execution proof; they
cannot escape into theorem premises or conclusions. Their names must be
distinct from the callback and from `result`; a return-valued callback parameter
also cannot be named `result`. Additional theorem parameters remain outside
this slice. Const-qualified pointer returns and parameters use the same C
spelling in callbacks, named contracts, and execution proofs.

When the target contract declares resource proof parameters, the conclusion
introduces one arbitrary instance per parameter with an `as` map keyed by the
contract's parameter names:

<!-- verified-example: mdtests/c_contract_executes_counter.md -->
```click
theorem lift(callback: int32 (*)()) executes callback() {
    requires Exact(callback);
    ensures Progress(callback) as { cell: k } by {
        step(Exact(k));
        have k.revision == old(k.revision) + 1 by { assumption(); }
        apply(int32_increment_strictly_increases(old(k.revision), 2147483647));
        simp();
    }
}
```

`k` is the only name for that instance inside the block, and the theorem proves
the refinement for an arbitrary such instance. The target's own spelling `cell`
is not in scope: nothing enters an execution proof block implicitly. Every
target proof parameter must be named exactly once, and an introduced name
cannot shadow the callback, the call arguments, a theorem local name, or
`result`. The names do not escape the block. A target with no proof parameters
takes no map, though an empty `as {}` is accepted, and a map on such a target
is an error. Source and target parameter names are unrelated, and the target
contract may be declared later in the file. The
[counter refinement tests](https://github.com/lacker/click/blob/master/mdtests/c_contract_executes_counter.md)
demonstrate an exact field increment refined to progress while framing an
unrelated caller-owned counter. Unmentioned fields of the selected counter are
not implicitly preserved.

`executes` may also name a verified or explicitly external C function instead of
a callback parameter. The theorem then has no callback parameter and no
source-contract premise: the source is that function's own checked contract,
run by the single call step.

<!-- verified-example: mdtests/c_contract_executes_concrete.md -->
```click
theorem increment_is_exact() executes increment(int32* state) {
    ensures Exact(&increment) as { cell: c } by {
        step(increment(state), { first: c });
        simp();
    }
}
```

The conclusion chooses the form: a function address selects the concrete route,
a plain binding the abstract one. The proof state still starts from the target
contract's requirements and resources with the `as`-introduced instances bound,
and the call is the ordinary C call of
[Read and write resources](#read-and-write-resources), so the callee's own
binder names appear only on the left of its map and the introduced name on the
right. The written parameter list restates the C signature as well as the target
contract's interface; the callee must be verified or explicitly external in the
project; extra theorem parameters stay outside this slice; and every feasible
proof case must execute exactly one call, as in the abstract form.
`apply(increment_is_exact())` then introduces `Exact(&increment)` at a call site
exactly like a concrete `unfold(Name)` refinement theorem. This is the explicit
route for a target contract with proof parameters, which `unfold(Name)` refuses.
The [modeled-instance variant](https://github.com/lacker/click/blob/master/mdtests/c_contract_executes_concrete_model.md)
carries a tree instance through the same two maps.

Passing `&f` where a named contract is required does not always need such a
theorem. Automatic formation admits scalar propositions over current and
function-entry memory, resource-field reads on either of those states,
algebraic equalities, `match` over an algebraic value, and algebraic
pure-function arguments, provided every clause follows by an exact route.
`at(...)`, explicit memory snapshots, counted-resource populations, and range
folds stay outside it. When the contract declares proof parameters, formation
also requires the pairing between its parameters and the implementation's
binders to be forced: one implementation binder per parameter, same resource
family, equal arguments, and the reverse. Otherwise Click refuses and prints
the `executes` theorem that states the pairing.

## Requirements

Requirements are shared by all guarantees for the function.

Supported structural requirements:

<!-- verified-example: mdtests/pointer_range_segment_syntax.md -->
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

`aligned(pointer, n)` states that the pointer's address is a multiple of `n`,
a power of two. It is sugar for `address(pointer) & (n - 1) == 0`. Click
decides it from how the pointer was formed, never from its pointee type: a
successful heap allocation is 16-byte aligned; a declared local's block is
aligned for its type from its declaration, a struct local's for its
layout; a file-scope or static object's block is aligned for its type from
its creation; and a pointer reached through a parameter
needs an `aligned` clause in a contract or a `fact` in a resource. A
required complete-object clause `object(p)` for a struct type carries
`aligned(p, alignof(struct))` as a generated requirement: the caller proves
it and the function relies on it. A produced object and a resource body
state alignment explicitly, with `ensures aligned(result, n)` and
`fact aligned(p, n)`. A
constant byte displacement from such a base is then decided exactly, so
`aligned(p + 1, 8)` is refuted when `aligned(p, 8)` holds, and a symbolic
element step whose scale the alignment divides keeps it, so `aligned(p + i, 8)`
holds for an 8-aligned `struct pair *p`. Other symbolic displacements and
pointers without evidence stay undecided.

`requires` can also use Click propositions, but direct memory reads in
requirements are intentionally limited. If a precondition needs memory reads,
package it as a named predicate and unfold it at proof sites when needed.

## Read and write resources

Memory resources have viewed and owned resource elements. `views
base[start..end]` supplies persistent read access; `owns`, `consumes`, and
`produces` supply write access with the transfer behavior described below.
These are resource facts, not classical predicates, and are carried in the
verifier's resource context rather than copied as pure facts.

<!-- verified-example: mdtests/resource_context_write.md -->
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

These memory resource facts belong to the built-in memory family. The family
defines how resources entail, split, rejoin, transfer, and consume each other.
This keeps the user-facing memory syntax concrete while sharing the same
context machinery with non-memory resources.

Click also supports exact-match abstract resources:

<!-- verified-example: mdtests/token_resource_borrow_return.md -->
```click
abstract resource open_fd(fd: int32);
```

An abstract resource has no locally visible body and must use the explicit
`abstract resource` spelling. After declaration, `owns open_fd(fd)`,
`views open_fd(fd)`, `consumes open_fd(fd)`, and `produces open_fd(fd)` use the
same resource context. Arguments are type checked. Repeated equal owned units
form a quantity; a requirement for two units cannot be satisfied by one.
The function-level clause `constructs open_fd(result);` authorizes one
post-execution `construct(open_fd(result));` step to create exactly one owned
abstract token without consuming an input resource. The constructed token must
also be named by the function's `produces` contract.

An ordinary resource declaration requires a body shared by all equal units:

<!-- verified-example: mdtests/counted_resource_refcount_transitions.md -->
```click
resource object_ref(obj: struct object*) {
    owns object(obj);
    fact obj->refs == count(object_ref(obj));
}
```

Repeated owned clauses denote a quantity rather than a duplicate-ownership
error. Omitting a coefficient transfers one unit. An owned user-declared
resource may instead transfer an `int32` quantity explicitly:

<!-- verified-example: mdtests/symbolic_token_quantity_contracts.md -->
```click
owns amount of object_ref(obj);
consumes amount of object_ref(obj);
produces amount of object_ref(obj);
```

The coefficient must be provably nonnegative at the contract snapshot. Zero is
the resource identity and grants no authority. The body belongs to the
population as a whole, not once per unit.
`count(object_ref(obj))` is an `int32` expression naming the population size.
The example above therefore says that all references together own the object
and that its stored count equals their logical total. A wildcard argument sums
matching exact populations, so `count(pool_object(pool, _))` counts every
checked-out object belonging to `pool`.

A contract's net resource transfer changes the population count. For
example, `owns object_ref(obj); produces object_ref(obj);` is a one-unit
retain, while `owns object_ref(obj); consumes object_ref(obj);` is a one-unit
nonfinal release. Returning the new resource context is valid only when the
population body facts hold in the post-state, so these clauses cannot mint a
reference without the corresponding concrete counter update.

Once C execution returns, the remaining proof uses the post-return population
counts while retaining the body's ownership for closing open resources. The
new count does not itself establish any body invariant: the proof must still
show that the stored values agree with it. This return-count interpretation
comes from the contract's checked exit rule and requires no framing step of
its own.

`fold(object_ref(obj))` initializes a population of one from its body
resources. `open(object_ref(obj)) { ... }` temporarily exposes the one shared
body and requires it to be restored on exit without changing the population.
`unfold(object_ref(obj))` is the inverse lifetime operation and is allowed only
after proving that the count is exactly one; it exposes the body for a final
destructor or `free`. Ordinary retain and release operations use `open` rather
than folding or unfolding the body. Symbolic coefficients are not accepted on
memory, allocation, or recursively defined composite resources. Those
resource families need separate certified semantics rather than treating a
quantity as repeated clauses.

Population bodies preserved across opaque calls must have a resource footprint
determined entirely by the declared resource arguments. A body whose owned
range or contained resource is selected by mutable memory, a changing guard,
or a recursive path is not supported across a call that can change that
selector. Click does not currently have transition authority that can retire
the exact pre-call footprint before activating the post-call footprint without
risking stale or duplicated ownership. Use a stable-footprint resource design;
support for dynamic population footprints is not part of the current language
contract.

Composite resources are declared resources with a body:

<!-- verified-example: mdtests/resource_without_body_requires_abstract.md -->
```click
abstract resource socket_open(fd: int32);

resource uncalled(flag: int32*) {
    contains socket_open(7);
    owns flag[0..1];
    fact flag[0] == 0;
}
```

A resource may declare pure fields before its body clauses:

<!-- verified-example: mdtests/resource_fields.md -->
```click
resource buffer(p: int32*, capacity: int32) {
    field contents: List<int32>;
    field mark: Mark;
    field revision: int32;
    owns p[0..capacity];
}
```

Here `Mark` is the enum declared in the linked fixture. Fields have Click
types: supported unqualified C scalar/pointer types or algebraic types,
including instantiated generic types. Field names must be distinct from one
another, resource parameters, and body witnesses. Fields precede any guard
and cannot be declared inside it. Qualified C types, struct types/pointers,
arrays, and function-pointer field types are not supported in this slice.

Resources with fields are non-countable and intended for exclusive
instance-based ownership. Both `count(resource(...))` and quantities such as
`1 of resource(...)` are rejected. Field-free resources keep their existing
rules. Named ownership binds an exclusive instance with arbitrary typed fields:

<!-- verified-example: mdtests/resource_instance_bindings.md -->
```click
int32 identity(int32 value) {
    owns cell: marked_cell();
    ensures result == value;
    ensures cell.model == old(cell.model);
    ensures cell.revision == old(cell.revision);
} by {
    execute();
    simp();
}
```

Here `marked_cell` is declared in the linked fixture. `cell.model` reads the
currently owned instance's field; `old(cell.model)` reads its function-entry
state. Returning ownership does not itself promise unchanged fields; use an
explicit postcondition. Instance identity is distinct from field state, and
fields are symbolic Click values, not executable C ghost parameters.

Explicit callback applications such as
`step(Read(first))` transport ownership with fresh post-call fields constrained
by the selected contract. `unfold(cell)` exposes an instance's immediate memory
body and its facts; field names in the body denote that instance's fields.
For witness-free memory-only bodies, including guarded and matched bodies, unfolding consumes the named
instance without retaining an open handle. Current field projections require
owned instances; entry snapshots such as `old(cell.value)` remain available.
The legacy `fold(cell)` form uses the instance's entry-state fields as its
target, and checks the complete body ownership and facts. It does not require
an earlier unfold.

An explicit fold binds its result and supplies every field by name:

<!-- verified-example: mdtests/resource_cell_construction.md -->
```click
void init(int32* p, int32 value) {
    consumes p[0..1];
    produces c: cell(p);
    ensures c.value == value;
} by {
    execute();
    let c = fold(cell(p), { value: value });
    simp();
}
```

Here `cell` is declared in the fixture. The fold consumes its body ownership
and checks the body facts with the proposed fields. No earlier resource is
required. Rebinding a contract's resource name also permits changed fields
after C updates the memory; the name must not currently own another instance.
Field order is irrelevant, but missing, duplicate, unknown, or ill-typed
fields are rejected. Initializers accept C-valued and ADT-valued symbolic
expressions, including constructors, `old(c.model)`, matches, and pure-function
applications. For example:

<!-- verified-example: mdtests/resource_adt_construction.md -->
```click
let c = fold(cell(p), { model: Mark::Set(value) });
```

The complete declaration and proof are in `mdtests/resource_adt_construction.md`.
Pure-function applications remain symbolic;
fold checks the resource relation against the proposed value. Initializer
memory reads must be justified. A consumed name does not supply a current
field value; use an entry snapshot when that is the intended model.
An ordinary C call transports constructed resources through the explicit
binder map described under "Calls that transport named instances".

Guarded and constructor-matched memory-only bodies support explicit construction
and field updates with the same `let c = fold(...)` syntax. No earlier unfold
is required. Guarded bodies support the
existing single `if` guard with an empty false case. Fold/unfold requires proof
of the selected guard case. The false case exposes no memory or body facts;
unfold consumes the instance in either case. A fold checks the guard with the
proposed fields and must justify the selected body's ownership and facts.
Post-return folds are checked separately against each return path's memory,
ownership, and guard assumptions. Every returning path must restore the
ownership promised by the contract; a sibling's fold cannot supply it.
The regression is `mdtests/resource_fields_guarded_memory_body.md`.

A field-bearing body may instead match one algebraic field:

<!-- verified-example: mdtests/resource_fields_match_memory_body.md -->
```click
resource cell(p: int32*) {
    field model: Maybe<int32>;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => {
            owns p[0..1];
            fact p[0] == value;
        },
    }
}
```

Here `Maybe<T>` is declared in the linked fixture. Arms must cover every
constructor exactly once. Bindings are scoped to their arm and have the
constructor's instantiated types, including pointers and nested ADTs. They
cannot shadow resource parameters or fields. Fold/unfold requires constructor
evidence for the actual instance field (for example,
`c.model == Maybe<int32>::Some(expected)`); an unknown field does not cause
implicit proof-by-cases. Only the selected arm's memory and facts are exposed.
An explicit fold selects the arm from its proposed model, so an update can
change constructors when the new arm's ownership and facts are established.
The regression is `mdtests/resource_conditional_construction.md`.
The same ownership and path-local return checks apply.
Match arms can also expose named, directly recursive child instances:

<!-- verified-example: mdtests/resource_recursive_children.md -->
```click
resource tree(p: int32*) {
    field model: Tree;
    match model {
        Tree::Leaf(value) => { owns p[0..1]; fact p[0] == value; },
        Tree::Branch(value, lp, lm, rp, rm) => {
            owns p[0..1];
            owns left: tree(lp);
            owns right: tree(rp);
            fact p[0] == value;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}
```

Here `Tree` is declared in the fixture. Give the exposed children independent
names, then pass their owned instances explicitly when constructing a parent:

<!-- verified-example: mdtests/resource_independent_children.md -->
```click
unfold(root) as { left: l, right: r };
unfold(l);
execute();
let l = fold(tree(left), { model: Tree::Leaf(2) });
let root = fold(tree(p), { model: old(root.model) }, { left: l, right: r });
```

`unfold(root) as { ... }` consumes `root`, exposes its immediate memory, and
introduces folded children. No parent handle or `root.left` path remains.
Each selected-arm child must be named exactly once. An introduced name must
not already own a resource. `unfold(l)` exposes the child's immediate body;
an arm with no children needs no bindings (explicit `as {}` is also accepted).

The third fold argument maps child slots to owned resource names. Folding
consumes those children and the parent's immediate memory, checking each
child's family, arguments, and fields against the proposed model. Replacements
and reordered children are allowed when those checks hold. Missing, duplicate,
unfolded, or mismatched children are rejected. A leaf omits the empty child map.
The new parent need not have existed before; `consumes l: tree(left);` names
an input child without promising to return it separately.

Parent-qualified resource handles such as `root.left` are not supported.
Unfolding a recursive body requires `as { ... }` to name its selected children;
refolding requires the explicit child map. Unfold consumes the parent, so it
cannot be projected or unfolded again unless a new owned parent is constructed.

Each child currently uses the parent's resource definition. Equations for all
child fields must bind them to immediate constructor fields of the matching
types. In particular, the matched model strictly descends to a proper submodel.
Child arguments may be read-only C expressions, including stored pointer
fields such as `p->left`. Loads must be readable from the immediate body's
owned memory, not from a still-folded child or unrelated ambient ownership.
Fold checks this memory before interpreting the child arguments. Expression
safety and path premises must be proved; argument evaluation does not split
the proof into cases. See `mdtests/resource_tree_node_init.md`.
Mixed resource families, witnesses, nested resource matches/guards, arbitrary
match scrutinees, and passing child paths as contract arguments remain
unsupported. No operation automatically unfolds an entire recursive structure.

A declaration alone grants no ownership, and binding an instance does not
implicitly expose its memory body.

### Calls that transport named instances

A C function whose sidecar declares instance binders is called with an
explicit map from each of those binders to an instance the caller owns:

<!-- verified-example: mdtests/c_call_binder_transport.md -->
```click
step(increment(state), { first: c });
```

The first argument is the call as written in the source, so the step still
selects one call statement: the frontier must be a call to that function with
that many arguments. The map is required whenever the callee declares any
`owns`, `consumes`, or `produces` binder, and a callee with none takes no map.
It is the only source of bindings; nothing is matched by name, by position, or
by search. Missing, duplicate, unknown, wrong-family, and unowned entries are
rejected where they are written.

The transition is the one a named contract's proof arguments already take.
A `consumes` binder removes the caller's instance. An `owns` binder returns
the same identity with fresh post-call fields, related to its entry fields
only by the callee's guarantees, so a field the callee does not mention is
unknown afterwards. Caller instances the map does not mention frame unchanged.

An instance the callee `produces` does not exist before the call, so the
caller introduces it with `let`:

<!-- verified-example: mdtests/c_call_binder_transport_produces.md -->
```click
let node = step(init(p, left, right, value), { l: a, r: b });
```

The introduced name is an ordinary owned instance afterwards: it can be folded
into a parent as a child, or returned by the caller's own `produces` clause.
A `produces` binder that no `let` introduces is an error, and so is a `let` on
a call that produces nothing. A callee that produces more than one instance is
not yet callable this way. The callee's binder names come from its own
sidecar, so that sidecar must be declared before the proof that calls it.

A composite body may instead have one top-level guard:

<!-- verified-example: mdtests/recursive_conditional_resource.md -->
```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        contains list(node->next);
    }
}
```

A body may also bind an existential pointer with `let name: type where
proposition;`. The witness is in scope for every later clause, and the `where`
proposition is one of the body's pure facts:

<!-- verified-example: mdtests/resource_witness_unfold_fold.md -->
```click
resource packed(node: struct node*) {
    owns node->word;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}
```

This is how a resource describes a pointer packed into an integer word, such
as a tail pointer with a mark bit or an `rb_node` parent with its color. The
witness needs no syntax at `fold` or `unfold`. Unfolding binds it to a fresh
symbolic pointer constrained by the `where` fact, and the program's own cast
`(struct node*)(node->word & ~1)` then recovers exactly that pointer. Folding
binds it to the recorded origin of the word the `where` fact relates it to, so
after `node->word = (unsigned long)tail;` the witness is `tail`. A word with no
recorded origin cannot fold, and the diagnostic names the missing body fact.

There is no `else`: when the guard is false, the body is empty. The guard must
be load-free, because it decides which memory resource facts exist and therefore
cannot depend on reading that same memory. A guarded body may directly contain
the resource being defined. This direct self-recursion is the supported
recursive form; unguarded recursion and mutual resource cycles are rejected.

`observe` keeps a guarded resource opaque when neither the guard nor its
negation is known. Explicit `fold` and `unfold` require the guard to be decided.
When active, they expose or consume exactly one body layer, leaving a recursive
child such as `list(node->next)` folded. This makes proof cost depend on the
number of explicit list operations, not the unknown length of the list.

Holding the folded abstract token exposes its immediate pure facts and viewed
resource facts, but not its owned contained resource facts. Hidden contained
owned resources also expose direct `contains(...)` and `separate(...)` pure
facts. In an explicit proof script,
`observe(uncalled(flag));` non-destructively records this projection while
keeping owned contained resources hidden. `unfold(uncalled(flag));` consumes the
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

<!-- verified-example: mdtests/callback_resource_complete_once.md -->
```click
int32 complete(int32 cb) {
    consumes can_complete(cb);
}
```

Resource facts are written with resource verbs:

<!-- verified-example: mdtests/token_resource_borrow_return.md -->
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
using `views` borrows the caller's viewed or owned element for that call. It
does not consume the original element or create a second persistent view when
the call returns. A view that was already present in the caller remains
persistent. Owned elements are transferred by `owns`, `consumes`, and
`produces`.

Fixed-size heap objects add the built-in owned resource
`allocation(base, bytes)`. It is exclusive authority and responsibility for
one live heap lifetime; it does not authorize memory access. Complete access is
spelled separately with `object(base)`. Allocation authority cannot be
`views`-ed or duplicated, and a verified function may not silently drop it:
the authority must be returned (possibly inside a composite resource) or
consumed by an actual `free`.

<!-- verified-example: mdtests/conditional_resource_body.md -->
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
the owned wrapper before calling `free`. Once a read-only helper returns, that
call-scoped borrow is over, so the caller may immediately pass its retained
owned wrapper to the destructor. Conversely, an independently held direct or
composite view of the same allocation remains live and makes `free` fail at the
deallocation statement; views proved separate survive.

When the guard is not known at function entry, a proof-level `if` can split on
it even if the C body is branchless. Each proof case unfolds the matching
resource body: the empty branch certifies operations such as `free(NULL)`, and
the active branch exposes the resources those operations consume. Exact
contract certification checks both cases independently, so this does not add
a precondition or require rewriting the C control flow. The same condition
guards the mutable footprint inferred from the resource. At an opaque call,
Click decides the guard before evaluating its pointer and range expressions;
an inactive body therefore contributes no footprint.

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

This is intentionally not a complete resource system. Memory permissions have
no fractional form, and there are no general ownership predicates, general
allocator APIs, or user-defined resource algebras. Exact struct allocation and
runtime-sized `int32` arrays are the
supported heap slices. `loadable` remains a separate concept from memory
permission: loadability proves an access is in bounds, while memory resources
authorize the access.

## Propositions

Click proposition connectives are words:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
result == x and not (result != x)
result == x implies result >= 0
forall (k: int32) { 0 <= k and k < n implies p[k] == old(p[k]) }
exists (k: int32) { 0 <= k and k < n and p[k] == x }
```

Do not use C logical operators such as `&&`, `||`, or `!` in Click
propositions. Those remain C-fragment syntax.

Range proposition helpers:

<!-- verified-example: mdtests/pure_click_functions.md -->
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

<!-- verified-example: mdtests/exists_and_symbolic_any.md -->
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

<!-- verified-example: mdtests/write_second_old_keeps_first.md -->
```click
ensures p[0] == old(p[0]) by auto;
ensures forall (k: int32) { 0 <= k and k < n implies p[k] == old(p[k]) } by auto;
```

Inside `old(...)`, `result` is unavailable.

Contract expressions accept the unsigned narrowing cast `(uint32)x`, including
`old((uint32)p->value)`. The operand must be
a current C expression; put `old(...)` or `at(...)` around the whole cast to
select another snapshot. A 64-to-`uint32` cast retains the low 32 bits, rather
than requiring the source value to fit. Casts retain their selected memory
snapshot even when the underlying field is subsequently updated.

When `old(p)` is passed as an array argument to a pure Click function or
predicate, it becomes an entry-state Click array ref. For example,
`permutation(p, old(p), 0, 2)` compares post-state `p` to entry-state `p`.
See [Surface Click and Kernel Click](../../concepts/surface-and-kernel.md).

## `c(...)`

### File-qualified C objects

A `verifying` declaration may introduce a file alias:

<!-- verified-example: mdtests/qualified_static_resource.md -->
```click
verifying "left.c" as left;
verifying "right.c" as right;

resource both() {
    owns &left::count[0..1];
    owns &right::count[0..1];
    fact right::count == 19u64;
}
```

Declare the alias before using it. `counter::count` refers to the file-scope
C object declared in `counter.c`, including a private `static` object. The
alias is only a naming mechanism: it neither creates a module nor grants
ownership. One resource can own objects from several files. Ordinary calls
still need their declared resources, supplied initially by the program-entry
proof or transferred by a caller.

Use the existing memory syntax: `&counter::count[0..1]` owns the storage of a
scalar, `cache::entries[0..16]` owns array elements, and
`counter::state.value` names a struct field resource. Owning a pointer variable
is different from owning the memory to which its value points. Resource facts
describe any contents that the resource's abstraction promises to clients.

Qualified objects also work in expressions, including `old(counter::count)`
and `counter::state.value`. Private objects with identical names in different
files remain distinct; qualifications of the same external object retain its
shared identity. This does not make private names visible in another C file.

A mutating wrapper can transfer its private field to a pointer-taking helper
and return ownership with the updated contents:

<!-- verified-example: mdtests/private_state_mutation_reset.md -->
```click
unsigned long left() {
    owns left_file::state.value;
    ensures left_file::state.value == old(left_file::state.value) + 1u64;
    ensures result == left_file::state.value;
    ensures result == old(left_file::state.value) + 1u64;
} by { execute(); simp(); }
```

Here `left_file` aliases the C file containing `state`; its unchanged C wrapper
calls `bump(&state)`. Ownership is transferred, not recreated on each call.
The fixture covers repeated calls, reset, and another file's independent
`state`. An implicit 64-bit integer return conversion to `int` requires proof
that the value is representable: signed sources need both bounds, unsigned
sources need the upper bound. This differs from the low-bit `uint32` cast.

For a function-local static, include the function name:

<!-- verified-example: mdtests/qualified_function_static_ownership.md -->
```click
owns &counter_file::increment::calls[0..1];
```

This names the same storage as the unqualified `calls` inside `increment`.
Callers can transfer its ownership, and expressions such as
`old(counter_file::increment::calls)` refer to its value. Qualification grants
no access by itself and never initializes or replenishes the resource.
Ordinary automatic locals and parameters cannot be named this way. If several
block scopes in a function declare statics with the same name, the reference
is rejected as ambiguous.

This syntax supports file-scope and function-local static scalars, scalar
arrays (including multidimensional arrays), and struct objects. It does not
qualify functions as values or arrays of structs.
Aliases must be unique and cannot share a name with a specification datatype.
Existing unqualified references and `verifying "file.c";` remain unchanged.

### Explicit C binding references

`c(name)` explicitly refers to the binding named `name` in the verified C
program. It is distinct from Click built-ins and contract bindings with the
same spelling. In particular, bare `result` is the function's contract result,
while `c(result)` is a C parameter or local named `result`.

C locals exist only while they are in scope. After function exit, refer to a
local through a recorded program point:

<!-- verified-example: mdtests/statement_at_snapshots.md -->
```click
result == at(statement(1).entry, c(result))
```

The AST retains this distinction; `c(result)` is not converted to an ordinary
string variable and cannot be reinterpreted as contract `result`. Expansion
uses this spelling when an explicit proof must name an overlapping C
binding.

Returning a pointer does not extend an automatic object's lifetime. A returned
pointer must refer to storage that outlives the call, such as caller-provided,
static, or live heap storage; a postcondition that dereferences a returned
pointer to a callee local is rejected.

## `at(...)`

`at(selector, expression)` evaluates a contract expression at a selected visit
to a program point. In a proposition position, `at(selector, proposition)`
evaluates the complete proposition at that visit:

<!-- verified-example: mdtests/statement_at_snapshots.md -->
```click
at(function.entry, x)
at(loop_label.entry, x)
at(statement(0).entry, x)
at(statement(0).exit, x)
at(statement(0).entry, p[0] == 7)
at(statement(0).entry, loadable(p[0..n]))
```

An execution proof can give its current frontier state a local name and use
that bare name as a selector later:

<!-- verified-example: mdtests/proof_mark_current_frontier.md -->
```click
mark before_write;
step();
have p[0] == at(before_write, p[0]) + 1 by simp;
```

`mark` is a simple tactic and does not move execution. Its name is scoped to
the proof, cannot be rebound, and is not an `execute_until` target. Bare
`at(before_write, ...)` therefore means a proof-local mark, while
`at(loop_label.entry, ...)` continues to mean the entry of a named source
region.

`at(function.entry, expression)` is equivalent to `old(expression)`. The
proposition form snapshots every state-relative part of the proposition
together. This matters for propositions such as `loadable(...)`: both the
address expression and the memory in which it is loadable come from the
selected state.

The selected snapshot is a complete recorded C state, not only a memory
snapshot. Inside `at(...)`, reassigned parameters and declared scalar, pointer,
and array locals resolve to their values in that snapshot. Outside `at(...)`,
function parameter names retain their ordinary contract meaning.

`at(loop_label.entry, expression)` is currently supported inside invariants for
that same labeled loop code region. It evaluates `expression` at the visit just
before the loop region starts, then reuses that snapshot for invariant entry and
preservation checks. Inside an explicit `preserve` proof, the same spelling
continues to denote that pre-loop snapshot; the current arbitrary loop-head
visit is available through the ordinary unwrapped expression.

The expression and proposition forms of `at(statement(N).entry, ...)` and
`at(statement(N).exit, ...)` are currently supported in explicit proof-script
claims after deterministic execution records that statement snapshot.
`step()`, `execute_until(...)`, and `execute()` all record every
deterministic statement boundary they cross. Executing an annotated loop uses
its verified abstract rule and records both `at(loop_label.entry, expression)`
and the unique post-loop state `at(loop_label.exit, expression)`. Branches still
require explicit arm proofs and a checked join before a unique exit snapshot
exists.

`execute_until(statement(N))` starts at the current execution frontier, so it can
follow earlier `step` or joined `branch` steps. The
target must be forward and reachable on that selected path; it cannot be used
to rewind execution or enter an unselected branch.

## Pure Click functions

Click functions are specification-level value definitions, not executable C
functions. Their parameters are Click-native binders and therefore use
`name: type`, unlike attached C function signatures.

<!-- verified-example: mdtests/pure_click_functions.md -->
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

Recursive pure functions must declare a well-founded measure. One supported
form is a natural-number measure:

<!-- verified-example: mdtests/pure_recursive_function.md -->
```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}
```

Every direct or mutual integer-recursive edge must pass a nonnegative measure
strictly smaller than the caller's. This form restricts the measure to one
named `int32` parameter and recursive components to `int32` parameters and
results.

A recursive algebraic datatype parameter can also be the named measure. After
matching it, recursive calls may pass algebraic fields bound by that match;
nested matches on already-smaller fields, multiple recursive fields, and
mutually recursive datatype groups are checked the same way. Calls remain
symbolic. Explicit `unfold` exposes one defining equation and leaves the next
recursive application opaque, so verification never guesses a recursion
depth. This total value semantics is intentionally different from
partial-correctness C recursion.

General properties of symbolic recursive calls use theorem-level
`induct(parameter) as hypothesis`. For `int32`, induction is explicit and
strong: applying the local hypothesis checks a nonnegative strictly smaller
argument and the theorem's substituted requirements. For a recursive
algebraic parameter, `induct` takes an exhaustive constructor-arm block and
makes the same theorem available at each immediate recursive field:

<!-- verified-example: mdtests/algebraic_structural_induction.md -->
```click
induct(xs) as ih {
    List::Nil => { /* base case */ }
    List::Cons(head, tail) => {
        apply(ih(tail));
        /* inductive case */
    }
}
```

Constructor arities and exhaustiveness are checked, arm bindings are lexical,
and multiple recursive fields each receive an induction-hypothesis instance.
Mutual induction across different datatype families is not yet generated.
`simp` does not invent induction, and a pure function's `decreases` clause
remains definition-totality evidence rather than a theorem about the result.

Function contracts may also use contract-level `let` bindings:

<!-- verified-example: mdtests/contract_let_bindings.md -->
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
`owns`, `views`, and region proof blocks. A contract-level let cannot reuse a C
parameter name or an earlier contract-level let name. Explicit type annotations
are checked when the binding is evaluated.

Use `old(...)` in the binding when the abbreviation must capture an entry-state
value. For example, `let data = old(owner->data);` gives later postconditions a
stable backing pointer even if the current `owner` metadata changes.

Proposition clauses may also use witness lets:

<!-- verified-example: mdtests/contract_let_where.md -->
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
rejected in `loadable`, `owns`, and other memory-segment expressions until
Click has a contract-wide witness environment.

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

<!-- verified-example: mdtests/composite_resource_struct_owned_buffer.md -->
```click
consumes object(owner);
fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
```

`object(owner)` is layout-aware: it denotes the imported C struct's aligned
size without exposing byte offsets or pretending that a pointer field is a
pair of source-level `int32` fields. Use `owner->field` for one field and
`object(owner)` for the complete object. When a proof exposes the object's
cells, wide integer fields take their own type while pointer fields are
held as pointer-width words that read back as pointers; the field's source
spelling is unaffected. Explicit ranges such as
`p[0..count]` remain the normal spelling for array storage.

Surface Click also has documented low-level memory reads for addresses that do
not have a recoverable C source place:

- `load_int32(pointer)` and `load_uint8(pointer)`
- `load_uint32(pointer)`, `load_int64(pointer)`, and `load_uint64(pointer)`
- `load_int32_pointer(pointer)` and `load_uint8_pointer(pointer)`
- `byte_offset(pointer, bytes)`

`address(pointer)` is the `uint64` integer representation of an object pointer
under the LP64 profile. It is the spec spelling of the C cast
`(unsigned long) pointer` and denotes the same kernel term: the address keeps
the exact source pointer, so `address(p) == address(q)` is decided exactly as
`p == q`, `address(p) == 0` as `p == 0`, and a comparison with an integer that
has no pointer origin stays undecided. Contracts use it to describe words that
hold a pointer in integer form, such as `ensures node->word == address(next)`
or, for a tagged word, `requires node->word == address(next) + 1`. Tag
operations on such words (`+`, `|`, `& ~m`, `& m`) and the cast back to a
pointer are checked rewrites whose obligations come from `aligned`; the
memory model describes the rules. The tag set with `|` may be a constant or
a masked read `x & m`, as in rbtree's `rb_color(rb) | (unsigned long)p`,
whose bound is the mask; two words whose tags are so bounded compare unequal
when their pointers are distinct and both aligned past the bound. A mask
must clear the whole tag: `& ~1` on a word tagged with 3 is refuted rather
than producing a word that still carries bit 1.

The low-level reads and `byte_offset` are Surface Click escape hatches, not
Kernel Click syntax. The canonical
renderer prefers `owner->field` whenever imported layout provenance identifies
the address. Expansion may emit a low-level read only when no source field
place is available.

Concrete folds are unrolled. Symbolic folds remain `RangeFold` value terms in
the kernel and can be reasoned about by supported fold laws.

## Predicates

Predicates return Click propositions:

<!-- verified-example: mdtests/sorted_predicate.md -->
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

<!-- verified-example: mdtests/sorted_predicate.md -->
```click
ensures sorted: sorted_range(p, 0, n) by {
    execute();
    unfold(sorted_range);
    simp();
}
```

Loop invariants are declared by the `loop` tactic when execution reaches that
loop. Predicate bodies needed by the loop rule can be exposed in its
`initialize` and `preserve` proofs:

<!-- verified-example: mdtests/loop_sorted_range_invariant.md -->
```click
by {
    loop {
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
}
```

Either phase may be omitted, in which case Click supplies bounded automation
for that phase. `click expand` at the `loop` keyword materializes all omitted
phase proofs together.

Like pure Click functions, predicate array parameters are Click array refs.
A predicate can compare two arrays from different memory states when its caller
passes arguments such as `p` and `old(p)`.

## Write footprints

A function's externally visible write footprint is exactly the memory its
contract owns. There is no separate effect clause: `owns` permits stores and
reads, `views` permits reads, and a store outside the owned memory fails at
the store. The retired `modifies`, `preserves`, `mutable`, and `immutable`
effect spellings and the `frame` tactic are parse errors whose diagnostics name
this ownership form.

Contract segment expressions are evaluated at function entry, so a shifted
segment such as `owns (owner->data + owner->len)[0..2]` continues to denote the
old two-cell tail after `owner->len` changes. Footprint matching uses proven
pointer equalities, including unchanged field loads across a finite chain of
certified memory effects.

A narrow write inside a wider range is spelled as a view of the whole plus
ownership of the piece:

<!-- verified-example: mdtests/field_derived_precise_effect_after_metadata_write.md -->
```click
views owned_buffer(owner);
owns owner[0..1];
owns (owner->data + owner->len)[0..2];
```

Callers then frame the viewed remainder with no clause and no tactic. A
function that owns no memory must not write memory that was live at entry;
this is checked when the function contract is certified, so callers preserve
memory across a read-only callee with nothing to declare. Stack locals and
initialization writes to a function-fresh allocation are internal and never
part of the footprint. Ownership never waives allocation lifetime obligations.

File-scope and static storage is not caller memory, so a contract that declares
resources may store into such storage only inside the cells it owns: a `views`
clause, or ownership of a neighboring cell, does not authorize the store.
Resource slices of global and static arrays use the array's declared element
width, so `owns bytes[0..1]` on a `uint8` array covers one byte.

A loop may declare resources of its own beside its invariants, in the same
`owns` and `views` spellings a contract uses:

<!-- verified-example: mdtests/loop_owns_clause_frames_other_owned_memory.md -->
```click
loop {
    owns p[0..n];
    invariant i >= 0;
    invariant i <= n;
}
```

A declared resource must be one the enclosing function already holds; a loop
cannot own what its function does not. The loop then has the shape of a callee:
its body executes owning exactly what the loop declared, with everything else
the function owns viewed rather than owned, so a body store outside the loop's
owned memory is rejected at the store. The loop's write footprint is the memory
it owns, so the function's other owned memory keeps its pre-loop value with no
invariant naming it. A loop that declares only `views` owns nothing and so
writes nothing. With no declaration, a loop inherits everything the function
owns, which is the default footprint an omitted clause already means.

Loop frames are described in [proof-workflow.md](../../concepts/proof-workflow.md)
and [memory-model.md](../../concepts/memory-model.md).
