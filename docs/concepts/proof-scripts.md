# Proofs and proof scripts

A Click contract says what must hold. Its proof clause says how Click should
establish it.

Use an omitted proof clause or `by auto;` by default. `auto` orchestrates C
execution, effect reasoning, and proposition reasoning through checked proof
operations.

Prefer smart tactics while authoring unless profiling identifies a hotspot.
Exact `using` blocks are ordinary Click and may be committed after expansion,
but manually listing every premise is not the normal starting workflow.

An omitted proof means `simp` at the point where the statement holds:

- `ensures P;` on a C function holds at function exit, so Click executes to
  it first. That is `by auto;`, the script `execute(); simp();`.
- `have P;` holds where it is written. It is `have P by simp;` and never
  executes C.
- `have P by auto;` also proves `P` where it is written. With no C to run
  toward the fact, `auto` first tries the solver, which refutes the integer
  negation of a linear `Integer` bound from the facts connected to it, and
  then `simp` (`mdtests/have_by_auto_refutes_a_linear_bound.md`).

A proof of one step needs no braces: `by T(args);` is `by { T(args); }` for
any tactic written as a call, as in `have 0 <= x by assumption();`. `click
expand`, `profile` and `audit` read it as that block, and an expansion that
needs the braces writes them. `by simp;` and `by auto;` are written without
parentheses, and a `simp` step in a block may be too: `simp;` is `simp();`.

`by simp;` does not execute C. For a whole-function proof, use `by auto;` or make the
sequence explicit:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
ensures result == x by {
    execute();
    simp();
}
```

A callback statement may lower to several checked operations. If a script
stops before its remaining callback calls, its diagnostic names a missing
resource or contract needed to continue, when a short checked continuation
finds one. The continuation is diagnostic only; the unfinished script is
still refused. A changed callback cell needs a contract fact for its current
pointer. Consuming the resource that supplied its view first makes the load
fail for missing read permission
(`mdtests/rb_augment_callbacks_helper_rejects_changed_cell.md` and
`mdtests/rb_augment_callbacks_helper_consumes_suite.md`).

Inside an `open(resource)` scope, a named resource fold after `execute()`
uses each returned path's state before the scope closes, just as a fold after
execution outside the scope does. A proposed field value must still match
that returned state (`mdtests/resource_instance_fold_after_return_in_open.md`).

## Smart and simple tactics

Smart tactics plan or search. The most common are `execute()`,
`execute_until(...)`, `simp()`, bare `apply(...)`, and bare `transport(...)`.

Simple tactics request one deterministic checked operation without planning or
search, and their checkers must be fast and output-sensitive. Paired operations
use `using` to mark that boundary:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
simp() using {
    i >= 0;
    i < n;
}
```

An empty `using {}` block is valid on every tactic that takes a list. It means
the tactic uses no pure premises, which is not the same as leaving `using`
off: `simp()` searches the context while `simp() using {}` uses nothing. `step()` is simple and executes the next statement with the whole
proof context visible to the kernel.
`execute()` and `execute_until(statement(N))` are its repetitions; expansion
replaces them with the corresponding sequence of `step();` tactics.

`simp() using { ... }` is still smart: the listed facts restrict its search,
and expansion replaces it with named simple rules. Common simple proposition
tactics are `assumption()`, `normalize()`, `rewrite(...)`, `intro()`, and
`contradiction(...)`. `assumption()` also closes a conjunction whose sides
are facts and a disjunction with one side a fact. A successful
expansion contains only those explicit rules and named theorem applications.

Bare `apply` retains explicitly proved premises in its generated `using`
list when the simple theorem checker needs them. For example, prove a
constructor inequality with `have ... by { normalize(); }` before applying
a theorem that requires it. Recognizing the fact during planning does not
replace that evidence (`mdtests/theorem_apply_retains_constructor_inequality.md`).

## Pure, fixed-state, and execution proofs

A pure proof reasons without a symbolic C state. A fixed-state proof reasons
against one fixed symbolic C state but does not advance execution. Pure
theorems use pure proofs; nested `have P by { ... }` proofs use fixed-state
proofs. Both can use simplification, theorem application, exact derivation,
logical tactics, and proof-level `if`; fixed-state proofs can additionally
transform logical resources.

In a pure theorem proof or a C postcondition proof, an introduced `int32`
binder may shadow an earlier name. After `intro()`, `x` names the newest
binding and `outer.x` names the previous binding of `x`; `outer.outer.x`
names the one before that. In a C postcondition, the outer name can refer to
the function parameter. The qualifier resolves to the retained binder
identity, including in a nested `have` and in its checked expansion. A
qualifier with no corresponding enclosing binding is rejected. A `have`
written after `intro()` stays inside that postcondition's binder scope.

Whichever kind it is, a proposition a step writes down is lowered against the
premises in scope where it is written: the claim's own `requires` and every
fact the proof has established before that point. That is what makes the
ordinary repair for a term Click cannot see is defined work the same way
everywhere — prove the missing fact with `have X by { ... }` before the step
that needs it, and the step then goes through, with no new syntax. A pure
theorem's `have` sees its theorem's `requires` and its earlier `have`s
(`mdtests/pure_have_sees_proved_facts.md`) exactly as a C proof's does
(`mdtests/c_proof_have_before_the_step.md`), and a refusal lists the premises
it actually consulted
(`mdtests/pure_have_reports_the_premises_it_consulted.md`).

Scope is the limit. A nested `have` body is its own scope: what it proves
justifies its own statement, and once the body closes only that statement
reaches the steps after it
(`mdtests/pure_have_body_fact_does_not_leak.md`). Inside `induct`, the
induction hypothesis is in scope as a quantified fact, not as a premise about
the current parameter values; `apply(ih(...))` is what turns it into one.

An execution proof carries a C frontier. The execution vocabulary is:

- `mark name;` to name the current state for later `at(name, ...)` expressions;
- `step()` for one simple deterministic transition;
- `execute_until(statement(N))` for a forward prefix;
- `execute()` for the remainder of the function;
- `branch ensuring { ... } then { ... } else { ... }` for the C `if` at
  the frontier and its single joined continuation; and
- `loop { ... }` for the C loop exactly at the current frontier.

Proof-level `if` splits reasoning; it does not execute a C `if`. Frontier-local
`branch` temporarily proves both C arms and then restores one current state.
A mark remembers a state the proof has already reached; it does not move the
frontier and is not an `execute_until` target.

Sequential early returns can be proved with nested proof `if` cases: the
returning arm reaches function exit, and the continuing `else` arm contains
the next case. The parser reads these `else` chains iteratively, and the
execution driver retains each completed case's checked join without adding
a recursive frame for the remaining path. Explicit proofs and `execute()`
expansions support at least 64 sequential returns. The driver still bounds
active recursive regions at depth 11; its diagnostic reports that recursion
bound rather than counting every written `else` block.

An execution proof may name the C body's own locals, not only the function's
parameters. A local of struct-pointer type is a memory base there, so
`have p->value == root->value` addresses `struct cell`'s layout exactly as a
parameter would (`mdtests/struct_pointer_local_has_a_layout.md`); a parameter
of the same spelling wins, because a contract is written against the
signature. A local the execution has not assigned yet has no value at the
frontier, and naming it is refused by naming the local
(`mdtests/have_names_a_local_before_its_assignment.md`).

## Splitting a model by constructor

`match value { Type::Variant(fields) => { ... } ... }` splits an execution proof
into one arm per constructor, with the constructor equation and fresh field
bindings on each arm's path. It may run at any frontier the proof has reached:
at unchanged function entry, after executed statements, and inside a loop's
`preserve` body.

An arm's bindings are in scope in every term the arm writes: `have` goals,
theorem arguments and `using` premises, `instantiate`, `extract`, `rewrite`,
`normalize() using`, the premises of a `simp() using` or `normalize() using`
inside a `have` body (`mdtests/have_body_simp_using_names_an_arm_binding.md`),
the clauses of a `loop` written inside the arm
(`mdtests/loop_clause_reads_arm_bindings.md`), and that loop's `initialize` and
`preserve` bodies (`mdtests/loop_phase_body_reads_arm_bindings.md`). A name that a `have` goal can see is a theorem
argument at the same point; `mdtests/theorem_argument_arm_binding.md` and
`mdtests/theorem_argument_arm_binding_algebraic.md` pin the pointer, integer,
and model cases.

A binding declared `struct ...*` is also a memory base in the arm, as it is in
a resource arm: `id->word` names the cell the arm's own `fact p == id`
identifies with `p->word`, and either spelling may be read in a goal
(`mdtests/egraph_resource_pointer_load_alias.md`). A binding of any other
declared type is refused as a field base, naming the type it was given.

<!-- verified-example: mdtests/proof_match_after_c_step.md -->
```click
step();
match c.model {
    Maybe::None => { contradiction(c.model == Maybe::None); },
    Maybe::Some(value) => {
        unfold(c);
        execute();
        let c = fold(cell(node), { model: Maybe::Some(value) });
        simp();
    },
}
```

Where the arms end depends on what is written after the `match`. With
nothing after it, each arm runs to the end of its region, function exit or
the loop's back edge, on its own path. With tactics after it, those tactics
are checked once: the live arms rejoin where they end, on their own when they
end in one state and through `ensuring { ... }` when they do not, and arms
that cannot rejoin are refused instead of each running the rest. See
[Opening a binder's model inside the body](loops-and-invariants.md#opening-a-binders-model-inside-the-body).

The constructor equation is an entry assumption of the whole function only when
the `match` ran before any C step. At a later frontier it holds on that arm's
path from the split onwards.

Either way it is a premise of the path, not a different entry state, so a
whole proof may sit inside one arm — including a ranked loop, which is the
shape the Linux insert fixup has: one `match` on the cursor's model at entry
and a `while` loop inside it. Contract certification discharges the arm's case
premise against the contract's own context and reuses the checked body as it
does for a flat proof
(`mdtests/loop_clause_reads_arm_bindings.md`, a ranked loop inside the `Node`
arm of an entry `match`).

The split also reads what the premises standing at that frontier force on the
scrutinee's instance. A path fact that refutes an arm's own fact says the
model is not that constructor, so the arm closes by `contradiction` on the
model; when refutation leaves one field-free arm, the split hands the path
that constructor. See [resources](resources.md) for the rule and
`mdtests/loop_body_refutes_an_unfolded_child.md` for a body that decides an
unfolded child this way.

The `contradiction` need not be the arm's only tactic. It closes the path it
stands on wherever it is reached, so an arm may run a `have`, a resource
unfold, or any other checked operation first to bring the refuting fact into its own
spelling, and then close. Nothing written after it on that path is executed or
proved (`mdtests/do_while_returns_rebound_resources.md`, whose loop body's
`Empty` arm unfolds the binder and then closes by `contradiction`). In a
`match` at the function's own level, whose arms otherwise each have to reach
function exit, the bridge may not run C: `have`s, unfolds and theorem
applications, then the `contradiction`. The arm is then excluded like one whose
only tactic is the `contradiction`, from the facts its bridge reached
(`mdtests/function_match_arm_closes_by_contradiction_after_a_have.md`,
`mdtests/function_match_arm_closes_by_contradiction_after_an_unfold.md`).

## Naming a call result

C often uses a call's result without ever storing it: `if (f(x))` and
`return f(x);` both leave the callee's guarantee and the branch or return
fact attached to a value the proof has no word for. The call step's `let`
binder names it. On a callee that declares a `produces` binder, the resource
output form names that instance; on a callee that declares none, the scalar
result form names the call's value:

<!-- verified-example: mdtests/call_result_in_condition.md -->
```click
let r = step(classify(x), { });
```

`r` is then an ordinary value name in `have`, `rewrite`, `normalize() using`,
and `simp` premises, on both sides of the `branch` that spells the C `if`. It
denotes the value the call returned, so it keeps its meaning after later
statements. Naming the result of a call whose result the C discards is an
error, as is reusing a name that is already a C local or a proof-local
binding. `examples/modeled-binary-tree` uses this to prove
`ensures result == heap_member(old(t.model), target);` for the recursive
`tree_contains`, whose two recursive calls appear only in a condition and a
return expression.

## Expansion and diagnosis

`click expand` replaces a selected smart tactic with a checked explicit proof.
When a post-execution tactic needs different proofs on different paths,
expansion may also replace the preceding execution script with its explicit
certificate. Each proof stays in the branch where it was checked, so a loop's
earlier guards are not evaluated again at function exit.
A post-execution `have` retains its established fact for later tactics. Smart
proofs recheck snapshot-qualified premise spellings, so a statement snapshot
recorded again by a loop cannot substitute a different fact for an earlier one.
A trailing `close_invariants` shared by several preservation paths can likewise
expand the preceding preservation script, placing each explicit closer in its
own branch. The loop's initialization and the script after the loop stay written.
`click profile` identifies slow tactics and distinguishes smart automation from
simple leaves. `click audit` checks that smart tactics across a project expand
into source that verifies normally. Use this workflow only after the
selected proof is correct: expansion is a checked optimization, not a way to
extract a partial result from a proof whose later tactics fail.

A `have` whose body neither closes the goal nor reports a failure of its own is
a declined body, and the message names the goal and what declined: the written
step, or "its body ran to the end with the goal still open", or that the body's
shape is not one the checked driver runs. The last case is usually a `simp()`
with something written after it; `simp()` closes a goal and is checked only as a
body's last step (`mdtests/have_body_declines_names_the_goal.md`).

The [proof tactics reference](../reference/tactics/index.md) is the exhaustive inventory
and compatibility guide.
