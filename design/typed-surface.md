# Typed Surface

Status: proposed 2026-11-25; direction agreed with the maintainer.

## Pipeline

Click turns proof text into kernel terms in three steps, each producing its
own Rust type:

| Step | From | To | Does |
|---|---|---|---|
| parse | text | **Syntax** | builds the tree as written; nothing is inferred |
| elaborate | Syntax | **Surface** | resolves names, infers every type and kind, fills in what the text leaves implicit, and checks; an ill-typed proof is one that fails to elaborate |
| lower | Surface | **Kernel** | resolves Surface names to kernel identities and builds the efficient form; infers nothing |

Going back:

| Step | From | To | Does |
|---|---|---|---|
| raise | Kernel | Surface | transcribes every kernel distinction and adds spellings from retained names and provenance |
| print | Surface | text | may leave out what elaboration would infer back, such as a cast or a `to_integer`; when unsure it prints the explicit form |

## Data flows one way

```
Syntax --elaborate (declarations in scope)--> Surface --lower (state at the position)--> Kernel --> proving
```

Each stage is computed once, before the stage that consumes it, and each
reads only its input and what that input legitimately depends on:

- Elaboration reads Syntax and the declarations in scope: the function's
  parameters, result and globals, the locals in scope at the clause's
  position, and Click's own definitions and binders. It never reads kernel
  state.
- Lowering reads Surface and the program state at the clause's position. It
  never reads Syntax and never decides a type.
- Proof code receives Kernel terms. It may have a clause lowered when its step
  is reached, since lowering resolves names against that step's state, but it
  never elaborates, never inspects Syntax or Surface, and never carries a
  typing context. Raising a proof back to Surface, for expansion or
  diagnostics, is a separate path out of the kernel.

A decision is made at the earliest stage whose inputs it needs, and later
stages read the result. When a decision is found in the wrong stage, move the
decision up to where its inputs are; never move its inputs down to where the
decision happens to be. Signs that a change is going the wrong way:

- it grows with the number of call paths rather than the number of constructs;
- code that should not care starts carrying something new, such as proof or
  resource code taking a typing scope;
- it makes two answers agree at the point of use instead of computing the
  right answer once, upstream.

The directory `src/surface` is older than this design and is named for the
surface language, not for the Surface layer: it holds the parser, lowering,
contract checking and the proof engine. Only `typed_surface.rs` and parts of
lowering are the Surface layer.

## The rule: inference reads context, lowering is compositional

Type inference depends on syntactic context. What `1` or `a - 1` means
depends on what surrounds it: the other operand of a comparison, the parameter
it is passed to, the declarations in the file. It cannot be decided one node at
a time, so it happens in elaboration, which sees the whole file.

Lowering is compositional. A node's kernel term is built from the node itself,
its children's kernel terms, and the program state it is lowered at, and from
nothing else: not its parent, not its siblings, not which function reached it.
The program state is resolution, not inference: `p->x` lowers to the read at
the address and memory version that state gives it, the same answer for the
same node at the same point.

This gives a test for the code. Lowering code that looks at a node's parent or
siblings, or behaves differently depending on its caller, is doing type
inference in the wrong place. The migration moves each such decision into
elaboration and records it in the Surface node.

## Every operation has its type

`int32` and `Integer` are different types, and a term's meaning includes the
type each operation works at and where each conversion happens. An int32
`a + b` wraps; an Integer `a + b` does not. `x == y` at int32 and
`to_integer(x) == to_integer(y)` hold in the same states but are different
terms, and a substitution or a tactic that works on one need not work on the
other: they are mathematically equal but not tactically interchangeable.

So Surface records every operation's type and every conversion as a node,
elaboration fills them from context, and lowering builds exactly that term.
The e-graph depends on it: congruence is sound only when each node names one
exact operation, and an equality class holds terms of one type, connected to
another type only through explicit conversions. An equivalence across types
is proved by checking, never applied by lowering.

Today the kernel's logical lowering breaks this for machine comparisons over a
compound operand: a spec's int32 `a + b == c` becomes
`IntegerEqual(observe(a + b), observe(c))`
(`condition_for_operand_views_in` in `src/kernel/machine_integer/comparison.rs`),
while the same C condition is `Compare { Int32, a + b, c }`. The raiser's
int32 and uint32 casts (`synthesize_int32_operand`,
`synthesize_uint32_operand`, `is_signed_variable_arithmetic32`) exist to steer
lowering back to the machine comparison. Fixing lowering removes them.

## The representations

- **Syntax** is the proof as written: structure, names and literals as
  written, point selectors and resource clauses as written, and source
  locations. It holds no types, no resolved meanings and no kernel values.
- **Surface** is fully typed. Every semantic distinction the kernel makes is a
  required field: a comparison is native at a format, Integer, pointer,
  address, algebraic, Bool or float; an operation is machine at a format or
  Integer (`Subtract { kind: Machine(Int32) | Integer, left, right }`); a
  literal has its type; a name says what it binds; a generic call names its
  instance. Each operation has one form. Program expressions are Surface
  forms shared by C, C++ and Rust. Surface holds no internal identities and no
  kernel values: it names things as source does (`foo`, `p->rb_left`,
  `old(x)`, `statement(2).exit`), and need not be efficient.
- **Kernel** is the compact form for checking: variables, addresses, memory
  states, interned subterms. It holds no strings.

Both are fully typed. The difference is that Surface is relative and Kernel
is resolved. A Surface term names things as the proof writes them, and means
something only given its context: the declarations in scope and the state at
its position. A Kernel term is the same meaning with every name resolved to
what it denotes there: `x` is a particular binding read at a particular state
point, `old(..)` is the entry point, a binder is a variable, and pointer
arithmetic is a byte offset on a known block. Lowering may also add what the
text leaves implicit, such as obligations, side facts and the memory reads
behind a C expression. Identities follow from resolution; interning and
sharing are the efficiency built on top. In short, Surface plus its context
is Kernel: lowering resolves a Surface term against its context, and raising
recovers the names from the identities' retained provenance.

Surface to Kernel is many to one: `old(x)` and `at(function.entry, x)` lower
to the same term. Kernel to Surface must never be: two kernel terms that
differ, such as a native and an Integer comparison, never share a Surface
term. The [raise-lower principle](../docs/internals/raise-lower-principle.md)
is then about Kernel and Surface alone: raising transcribes, and lowering
reads what Surface says.

## Current state

Click's trees today, `SurfaceProposition` (19 variants) and `SurfaceTerm` (48
variants, with 10 more in `ResourceSubject`), are what the parser produces and
what lowering reads. They are Syntax with extras mixed in:

- They leave these distinctions implicit:
  1. comparison kind (`SurfaceProposition::Comparison { left, operator, right }`);
  2. arithmetic kind and format (`SurfaceTerm::Subtract(left, right)` and its
     siblings);
  3. literal type (`SurfaceTerm::IntegerLiteral(String)`);
  4. which binding a bare name means (`SurfaceTerm::Binding`);
  5. a generic call's instance.
- They embed the kernel's own program-expression type,
  `SurfaceTerm::ProgramExpression(ProgramExpression)`, with 42 variants of its
  own. An operation therefore has two spellings, such as `SurfaceTerm::Subtract`
  and `ProgramExpression::Subtract`, which lowering treats differently, and
  Surface holds kernel values (`ProgramExpression::Value` carries
  `OldMachineTerm`s; `Field` and `CUnary` keep a `lowered` kernel form).
  `ProgramExpression` serves C, C++ and Rust alike; names such as `QualifiedC`
  and comments calling it a C fragment date from when Click verified only C.
- Inference runs twice. Validation (`src/surface/validation/`) infers types to
  check the tree and mostly discards them; declaration expansion keeps some,
  such as method resolution (`design/typed-method-resolution.md`). Lowering
  (`src/surface/lowering/annotations.rs`) infers them again from context, with
  `contract_expression_is_integer`, `contract_expression_click_type`,
  `contract_expression_is_algebraic`, `enum_program_value_type` and
  `contract_pointer_element_type`, and by which lowering function a caller
  uses (`lower_contract_expression_to_spec` makes `Subtract` machine
  subtraction, `lower_contract_integer_to_spec` makes it Integer
  subtraction). Lowering is not compositional.
- The parser does some type-driven work as it reads: struct types, typedefs
  and parameter types.
- Because the kind is settled only inside lowering, the raiser must choose text
  that lowering will reinterpret as the kind it started from. It does so with
  special cases in `src/surface/proof/surface_synthesis.rs` (`spells_integer`,
  `machine_spelling_lowers_to_integer`, `is_signed_variable_arithmetic32`, the
  `uint32` arithmetic cast, `integer_observation_comparison`'s ascription).
  Each covers cases seen so far; together they cannot be complete.
- "Elaboration" currently names the Surface-to-kernel bridge
  (`SpecElaborationContext`), which this design calls lowering.

The old names `ClickProposition` and `ContractExpression`, aliases of
`SurfaceProposition` and `SurfaceTerm`, were removed with this design.

## Migration

Today's trees become Syntax. The typed Surface is designed fresh, small, and
built up one construct at a time. Each stage is its own pull request and leaves
every test passing.

The migration reorganizes where decisions are made; it does not change what
they decide. Each step keeps the verifier's behavior: the same proofs pass, the
same kernel terms are produced, the same text is printed. A behavior change
joins a step only when today's behavior cannot be expressed in the new model,
and the step then names it. Where today's behavior is merely awkward, Surface
describes it as it is and the awkwardness is recorded for separate work. For
example, the kernel lowers a written int32 comparison over a compound operand
to an Integer comparison of observations
([Every operation has its type](#every-operation-has-its-type)); Surface
records that comparison's kind as elaboration chooses it today, and the
raiser's casts stay until that lowering is changed on its own.

1. **Name Syntax.** Rename today's `SurfaceProposition` and `SurfaceTerm` to
   `SyntaxProposition` and `SyntaxTerm`. A mechanical rename with no behavior
   change.
2. **Introduce Surface with comparisons and arithmetic.** Add the typed
   `SurfaceProposition` and `SurfaceTerm`, with required comparison and
   arithmetic kinds. While other constructs are not yet migrated, Surface
   carries them as a transitional `Untyped(SyntaxTerm)` node that lowering
   handles the old way. Elaboration produces Surface from Syntax; lowering reads
   the typed kinds and stops inferring them; the raiser fills them from the
   kernel term, and its guessing special cases for them are deleted.
3. **Program expressions.** Surface forms for program operations, shared by C,
   C++ and Rust, replacing the embedded kernel `ProgramExpression` and the
   `lowered` copies; Surface stops holding kernel values. Retire the C-only
   names.
4. **Literals.**
5. **Names:** a bare name says what it binds.
6. **Generic instances.**
7. **Finish.** Remove `Untyped`. Merge validation into elaboration and delete
   lowering's inference functions; lowering takes only Surface and is
   compositional. Rename `SpecElaborationContext`.

## Stage 2 shapes

Surface records the kind the kernel distinguishes, using the kernel's own
format enums:

```rust
pub enum ComparisonKind {
    Machine(MachineIntegerType), // OldConditionTerm::Compare at a format
    Integer,                     // IntegerLessThan .. IntegerNotEqual
    Pointer,                     // PointerEqual
    Address,                     // AddressEqual: address(p) == address(q)
    Algebraic,                   // AlgebraicEqual
    Bool,                        // BoolEqual
    Float(KernelFloatType),      // Float32, Float64
}

pub enum ArithmeticKind {
    Machine(MachineIntegerType), // OldMachineTerm::Binary at a format
    Integer,                     // IntegerTerm::Add, Subtract, ...
}

SurfaceProposition::Comparison { kind: ComparisonKind, left, operator, right }
SurfaceTerm::Binary { op, kind: ArithmeticKind, left, right }
SurfaceTerm::Negate { kind: ArithmeticKind, operand }
SurfaceTerm::Untyped(SyntaxTerm) // transitional, until every construct is typed
```

Bitwise operators and shifts exist only on machine words, so their kind is
always `Machine(format)`. A 32-bit equality is one kernel fact at either
signedness (rule K6); `Machine(Int32)` and `Machine(UInt32)` equalities lower
to the same term, which Surface-to-Kernel's many-to-one direction allows.

- **Elaborate** fills each kind with the rules lowering uses today, moved, not
  changed, so behavior stays the same: the expected-type rules of
  `docs/reference/language/index.md`, with operand types from the typing
  environment.
- **Lower** reads the kind: a `Machine` comparison or operation lowers its
  operands as machine words at that format, an `Integer` one as Integers. No
  operand inspection, no caller-dependent path.
- **Raise** copies the kind from the kernel term: `OldConditionTerm::Compare
  { format, .. }` gives `Machine(format)`, `IntegerEqual` gives `Integer`,
  `OldMachineTerm::Binary { format, .. }` gives `Machine(format)`, an
  `IntegerTerm` operation gives `Integer`.
- **Print** writes `to_integer(...)` or a cast exactly where the kind differs
  from what elaborating the bare text would infer. It asks the one function
  elaboration uses for that inference, so printing and elaboration cannot
  disagree.

## Stage 2 progress

Comparisons are typed first. `src/surface/typed_surface.rs` holds
`SurfaceProposition::Comparison { kind, left, operator, right }` with
`ComparisonKind::{Native, Integer, Algebraic, Sequence}`; operands are still
`SurfaceTerm::Untyped`. `elaborate_comparison`
(`src/surface/lowering/annotations/comparison_elaboration.rs`) chooses the
kind, with the rules lowering used, and also expands a struct equality into
its fields' equalities; `lower_surface_proposition` reads the kind and
inspects no operand.

`Native` stands for the shapes listed above as `Machine(format)`, `Pointer`,
`Address`, `Bool` and `Float`. Which of these a native comparison is, and its
format, is the C type of its operands, built bottom-up from them; that is
compositional, so lowering may compute it. It becomes a recorded field once
program expressions are typed Surface (stage 3). The kind elaboration records
now is the top-down decision: whether a written comparison is native, Integer,
algebraic or sequence, which depends on both operands at once.

Elaboration is being separated from the lowerer so that it can run with no
kernel. It reads outer names through the `TypeScope` trait
(`annotations/typing_environment.rs`), declared C types through
`Declarations` (`annotations/declarations.rs`), and does type synthesis
(`contract_expression_click_type`, the enum and pointer element types) on an
`Elaborator` (`annotations/elaborator.rs`), which holds only declarations,
specification definitions and recorded states. The lowerer delegates those
queries to it. Comparison elaboration (`elaborate_proposition`,
`elaborate_comparison` and the native operand forms) also runs on the
`Elaborator`, reading names through a `TypingEnvironment`, and asks lowering
nothing: the `LoweringQueries` bridge is gone. The untyped-pointer refusal,
pointer element widths, call argument types and generic instantiation all run
on the `Elaborator`, over the declared C types, the typing environment and
the recorded region results. Two kinds of answer still come from the lowering
context through `TypeScope`, transitionally, until the declaration scope
records them: what a name's pointer steps by when only its bound value says,
a struct pointer's object class (`bound_pointer_element`, a `PointerElement`
type rather than a value); and the scope at another program point for
`old(..)` and `at(..)` (`at_entry`, `at_point`), which the lowering context
builds as it always has. A generic instantiation's type-inference failure,
which lowering reads to classify an error, is handed back to the lowerer by
`with_elaborator`.

`annotations/elaboration_tests.rs` elaborates comparisons from declared types
alone, with no lowerer and no kernel state: Click binders declared in a
`TypingEnvironment` over `NoOuterNames`, and C parameters and their pointer
elements in the declarations.

A function contract's clauses can be elaborated from the function's
declarations alone. `Declarations::of_function` holds its parameters, result,
pointer elements and global and static objects (`GlobalDeclarations`), and no
entry state: a global's type, and a name's type at entry, come from the
declarations. `Elaborator::of_function` builds an `Elaborator` from them with
no lowerer. Debug builds check, for every clause `function_contract_summary`
lowers, that this elaboration equals the one its lowering context gives
(`check_contract_elaboration`).

`Elaborator::elaborate_clause` elaborates a whole clause, binder bodies
included: `forall` and `exists` become `SurfaceProposition::Quantified` and
the range forms `SurfaceProposition::Range`, each body elaborated with its
binder declared in the `TypingEnvironment`, at its declared type or, for a
range item, the type its endpoints give it (`range_bounds_are_uint64`). Debug
builds check at every binder lowering binds that elaborating the body with
the binder declared gives the Surface its lowered body context gives
(`check_binder_body_elaboration`).

Function contracts are elaborated before they are lowered. For each
requires, ensures and exceptional ensures clause, `function_contract_summary`
elaborates the clause once with `Elaborator::of_function` and
`elaborate_clause`, from the function's declarations alone, and lowers the
stored Surface: a binder form binds as before and lowers the body
elaboration gave it (`lower_elaborated_binder`), so no part of a contract
clause is elaborated inside lowering. The type-inference failure the
elaboration recorded is handed to lowering where in-place elaboration would
have left it. Debug builds check, at each clause and each binder body, that
the stored Surface is what elaborating that Syntax where it is lowered gives
(`check_stored_elaboration`). A requirement checked at a call site or as a
contract guard (`elaborate_requirement_proposition`) is elaborated the same
way, once and before it is lowered, from the callee's parameters; its
elaborator still reads a global from the entry state when the call site has
no global declarations, since call sites do not yet carry the callee's.

Every other clause lowered from Syntax, proof clauses, loop invariants and
statement annotations among them, is elaborated whole before any of it is
lowered: `click_proposition_to_spec_proposition` elaborates the clause with
`elaborate_clause` and lowers the stored Surface, and binder bodies lower
from theirs. Its scope is still the lowering context the clause is lowered
in, except for a proof clause of a C function written at a position the
front end records. The proof driver elaborates that clause itself
(`elaborate_proof_clause`) and hands lowering the Surface
(`ElaboratedProofClause`). Its scope is read from declarations alone
(`DeclaredScope`):
- The Click names the proof binds, from its integer and algebraic values.
- The C names in scope at that position, from the function's declarations
  and the locals the C front end records.

The positions, and the C names in scope at each:
- **An execution frontier:** the frontier's next statement. The C front end
  records a scope on each statement's site, where the statement starts. A
  `for` loop's test, step and body take its head's. Past the last
  statement, the scope is the end of the body.
- **A returned outcome, focused or as a fixed-state outcome case:** the
  parameters alone, recorded before the body opens. Once the function has
  returned, its locals have left scope.
- **A loop phase, its initialization or its exit:** the loop head's.

A fixed-state proof carries its position as a `ClauseScope`.

At a position, a C declaration has the type its value has in an expression:
- An array is a pointer to its first element.
- A struct-valued parameter or result is the pointer to its storage.
- A struct-valued local has none.

A binder the clause declares hides a C name of the same spelling. Debug
builds check that the driver's Surface is what lowering's own elaboration
gives (`lower_elaborated_proof_clause`).

A Rust function's front end binds a local by its spelling alone unless the
source binds that name more than once. For each such local it records the
declared type (`ImportedFunction::spelled_local_types`), and `Declarations`
reads that type for a name no binding resolves. That is enough for a Rust
clause at each of the positions above. Repeated names are not resolved per
statement yet.

Lowering still elaborates these clauses itself:
- C++ proof clauses, since that front end records no declarations yet.
- A contract refinement's clauses, which name a contract definition's
  parameters rather than a C position.

`Declarations` reads names' C types from kernel states (the entry state, the
entry values, and the state that declares the clause's locals) for names that
no C scope resolved, which is most names in function contracts and fixed-state
proofs. That is lowering reading kernel state to decide types, because
elaboration runs inside lowering. `GlobalDeclarations`
(`languages/interface.rs`) holds a function's global and static objects'
declared types, and debug builds check the two global lookups against it where
the lowering context has the function. Threading these declarations down
through every lowering path into proof and resource code was tried and
abandoned: it moved the input to the decision
([Data flows one way](#data-flows-one-way)). Instead, clauses are elaborated
before lowering, starting with function contracts, whose scope is fixed: the
function's parameters, result and globals.

Still to do in stage 2: elaboration runs where lowering reaches a comparison,
not as a pass before lowering; the raiser still returns Syntax and keeps its
guessing special cases; and arithmetic kind is still chosen by which lowering
function the comparison's kind calls.

## Open questions

- **Point-dependent types: answered.** Lowering's lookup (`c_variable_type`)
  reads only declared types: the function's result type, a resolved
  binding's type, parameters' declared types and entry values, locals at
  entry, and a state's local object types. A C local's type never changes as
  the program runs. What depends on the point is only which locals are in
  scope there, through blocks and shadowing. So elaboration needs a typing
  environment for the proof's position: the declared parameters and the
  locals in scope at it. In an execution proof that position is the step's
  frontier, so a proof statement is elaborated when its step is reached,
  still once and before lowering.
- **Abbreviation.** The printer needs one rule for when a cast or `to_integer`
  may be left out: exactly when elaborating the shorter text gives the same
  Surface term.
