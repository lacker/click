# Mathematical integers

`Integer` is Click's exact, signed mathematical number type for
specifications. It is separate from every C integer type and has no C storage,
ABI, machine width, or implicit runtime allocation. The kernel and standard
library may represent it internally in implementation-specific ways, but the
surface contract below is stable.

## Type and conversions

The public name is `Integer`; there is no `Int` alias. Existing `int` remains
the C `int32` type. Integer literals are arbitrary-size mathematical values
when their context is `Integer`. Machine values and Integer values mix only
where the type a result is used at expects an Integer: there each machine
operand of `+`, `-`, `*` and negation is observed with `to_integer` (the
[reference table](../reference/language/index.md#integer-specification-arithmetic)
lists the positions). `src/surface/parser/spec_arithmetic.rs` decides it
while parsing, from the expected types of comparison operands, declared
`Integer` parameters and fields, `-> Integer` results and typed `let`s; an
untyped `let` of machine arithmetic is refused. At an 8- or 16-bit position
(a typed `let`, an argument at its parameter's type, a pure function's body
at its result type) lowering marks the arithmetic spine with
`SpecExpression::at_machine_type`, so `+ - * & | ^ ~` over operands of that
type is the type's native operator (decision G2). A `match` arm and an `if`
branch are in the position of their match or conditional; an `if`'s
condition stays a proposition. So in an Integer position
`if c { a + 1 } else { b }` reads `if c { to_integer(a) + 1 } else {
to_integer(b) }`, an [Integer conditional](#integer-conditional), and
`to_integer(if ...)` written out observes the C conditional, with its
branches' C obligations.

An unused `Integer` parameter does not reinterpret a separately machine-typed
literal or expression. Expected-type propagation follows the expression and
its binding context; it does not leak across unrelated clauses.

`to_integer(x)` accepts each supported signed or unsigned machine-integer type
and preserves its numeric value. Signed `-1` and unsigned `4294967295u32` are
therefore different Integer values. Converting an already evaluated machine
value is total, but evaluating the argument retains all of its C definedness
obligations. In particular, `to_integer(x + 1)` does not discharge an
overflow obligation for `x + 1`.

Reverse conversions are destination-specific: `to_int8`, `to_int16`, `to_int32`,
`to_uint8`, `to_uint16`, `to_uint32`, `to_int64`, `to_uint64`, `to_int128`,
and `to_uint128`. A conversion
requires proof that the Integer lies in the destination's exact range. It does
not truncate, wrap, saturate, or insert an unchecked assumption. A symbolic
conversion requires both bounds, even in a reflexive proposition.

The same rule applies to conversions between `Nat` and `Integer`. `Nat` to
`Integer` is total; `Integer` to `Nat` requires a nonnegative proof. Checked
round-trip and arithmetic laws relate the types without identifying them by
implicit coercion. `Nat` remains the structural, nonnegative datatype used by
its own induction theorems.

`to_integer(a + b)` and `to_integer(a) + to_integer(b)` are distinct
expressions. A signed machine-addition equality needs evidence that the C
operation is defined; an unsigned equality must account for modular arithmetic.
No unconditional conversion distribution rule is sound.

### Structural arithmetic and spelling

Specification lowering retains mathematical addition, subtraction,
multiplication, negation, truncating quotient/remainder, and comparison
nodes, including constant operands. It does not compute `1 + 1` or replace
its equality with `2` by `true`. Arithmetic checking evaluates these claims;
constant subexpressions are evaluated once per shared node in the arithmetic
certificate's comparison form, with numeric work charged before computation.
Each shared node records whether it contains only literal arithmetic, computed
from its immediate children at construction. This lets checking keep symbolic
nonlinear atoms opaque without traversing their operand DAGs. A signed numeral such as `-2`
is a constant; negating a bound expression retains a negation node.

A rewrite can remove the last operand that supplied `Integer` context.
Structural comparison synthesis therefore gives its left operand an explicit
typed local expression, for example
`(let integer_value: Integer = 1 + 1; integer_value) == 2`.
The local's value is outside its binding scope, so this spelling cannot capture
names inside the value. The right operand inherits mathematical context.
Negation nodes similarly give their operands a typed local expression to
distinguish an operator over a constant from a signed numeral. Source printing
and reparsing must preserve the exact kernel nodes and comparison polarity.

### One form for comparisons of observations

A comparison of exact observations of one machine type, `to_integer(x) OP
to_integer(y)` or `to_integer(x) OP c` for a constant `c` in the type's range,
holds exactly when the native comparison `x OP y` or `x OP c` does
(`to_integer` is injective and order-preserving within each type). The kernel
states such a fact in one form, the native comparison
(`structural_native_comparison_of_integer_observation`, applied when a contract lowers and
again by `canonical_observation_form` on every kernel-built verification
condition). Written either way it is the same fact: `known()` closes
`to_integer(i) < to_integer(n)` from `i < n`, and a dropped `requires right !=
0u32;` beside `requires to_integer(right) != 0;` changes nothing. The order and
equality bridge theorems below therefore restate a fact rather than derive one.

Checking additionally evaluates literal arithmetic in the comparison view:
`to_integer(x) != -2147483647 - 1` can establish the native `INT_MIN`
exclusion while retaining its written subtraction. Compound proposition views
are indexed at admission with their source, so queries do not scan facts. Literal zero/unit
arithmetic identities join equality-graph classes without replacing either
term; generic substitution preserves operation and comparison nodes too.

Two cases keep the Integer form. A comparison whose native form folds to a
constant, such as `0 <= to_integer(u)` for an unsigned `u`, stays an Integer
fact so the type range it states can be cited. A comparison over Integer
arithmetic, such as `to_integer(a + b) <= to_integer(n)` or
`to_integer(a) + 1 <= n`, has no native form and stays Integer;
`to_integer(a + b)` is still not `to_integer(a) + to_integer(b)`.

Built-in checks (Rust panic checks, C definedness and branch decisions) read
machine facts, so filing an Integer fact (`PureFactContext::assume_condition`)
also files, beside it, the native fact it holds exactly when, in the cases
below. Each costs a shape match and at most a few exact lookups per
comparison the filed fact makes.

- A side that is the exact value of a machine `+` or `-` of observations or
  constants of one type reads as that operation's observation once the
  result lies in the type (`native_comparison_through_integer_operations`,
  the `integer_operation_identity` reading). `to_integer(a) <= 4294967295 -
  to_integer(b)` on `uint32`, which `have a <= 4294967295u32 - b` records,
  files `a <= 4294967295u32 - b`, the Rust add check. A range bound the
  operands' types imply needs nothing; any other must already be a fact, in
  either spelling or as the signed definedness fact
  (`IntegerOperationRangeBound`). So `x <= 18446744073709551614u64 - y`
  files nothing: its difference may underflow.
- A quantified fact `forall (k) { A(k) implies B(k) }` whose antecedent
  compares such an operation's exact value, `to_integer(k) <
  to_integer(len) + 1`, is filed again with that comparison read natively,
  `k < len + 1u64` (`native_antecedent_reading`). The range bound follows the
  rule above and may not name the bound variable. Built-in checks that match
  a resource definition's quantified body fact exactly, such as assembling a
  `cstr_at(p, len)` view, then read a fact a specification stated with
  Integer arithmetic
  (`mdtests/an_integer_stated_body_fact_assembles_a_c_string_view.md`,
  `mdtests/an_integer_stated_body_fact_needs_its_range_bound.md`). The work
  is the antecedent's conjuncts.
- A signed `int32`/`int64` definedness fact is filed when this fact is one of
  the two Integer bounds of its exact result (`integer_bounds_of_definedness`)
  and the other is already known, so execution steps over C `a - b` under the
  two `requires` bounds.

The reading is exact, not arithmetic: `to_integer(a) + to_integer(b) <=
4294967295` does not file the guard; state the guard with `have a <=
4294967295u32 - b;`
(`mdtests/a_built_in_check_accepts_the_integer_reading_of_its_condition.md`,
`charon_refused_panic_check_names_its_condition` in `tests/rust_import.rs`).

A narrow (`int8`, `uint8`, `int16`, `uint16`) value rides in the 32-bit word,
which is always the canonical carrier of its format, its zero or sign
extension ([kernel](kernel.md#one-meaning-for-a-narrow-value)). Its native
comparison is the signed 32-bit order of the words, as C's promotion to `int`
writes it, and that order is exact for every narrow value. The native form is
taken where its Integer reading recovers the narrow observation: a load of the
narrow type (or the variable naming one) or a conversion to it. A comparison
of a narrow binder, whose word does not name its format, keeps its Integer
form. For the same reason an `int32` or `uint32` observation of a narrow
load's widening reads as that load's narrow observation (rule W,
`SharedMachineIntegerTerm::value_reading`); the observation itself is built as
written (`IntegerTerm::from_machine` folds no conversion). So the native `old(bytes[0]) < 255` reads
as `to_integer(old(bytes[0])) < 255`. The Rust sum `old(bytes[0]) + 1` is a
checked narrowing of its 32-bit sum, a conversion node whose identity with
the sum is filed beside its range obligations, so its in-range identity
holds (`examples/rust-slices`).

The `Integer` arithmetic family reads a native comparison as the Integer
comparison of its operands' observations (`integer_affine_claims`). A 64-bit or
32-bit equality records no signedness, so it has both readings and a
certificate may use either; an order names its signedness, so a `uint32`
order reads as the `uint32` observations of its operands. The
special Integer rules read only the premises a node cites. `solve` refutes a
native goal as its Integer reading and spells each cited native fact through
its written operands, so an expanded certificate cites the facts as written
(`mdtests/solve_observes_an_operation_term_by_term.md`,
`mdtests/solve_proves_a_64_bit_equality_from_bounds.md`).

The checked `integer::uint32_less_equal_to_integer` and
`integer::uint32_to_integer_less_equal_implies_less_equal` laws preserve and reflect unsigned non-strict
order. Each requires the corresponding order premise. Unlike signed casts,
these observations retain values above `2147483647` through `4294967295`.
The proved library theorem `integer::uint32_to_integer_bounds(value)` supplies
`0 <= to_integer(value) <= 4294967295` from the native unsigned range.
These laws preserve the value of a wrapping expression as evaluated; they do
not make its observation equal an unbounded mathematical sum. Observation of
an undefined expression still requires its definedness prerequisites.

Strict unsigned order needs no bridge: `to_integer(left) < to_integer(right)`
is the native comparison `left < right` (see the single form for comparisons
of observations above). The checked
`integer::uint32_remainder_less_than_divisor` rule requires a nonzero native divisor and
bounds `value % divisor` strictly below it for every u32 dividend. Combining
these with `integer::uint32_to_integer_bounds` bounds the remainder's Integer observation
without changing its unsigned meaning or defining division by zero.

`integer::uint32_less_than_divisor_implies_remainder_is_value(value, divisor)` proves `value % divisor == value`
under the strict native unsigned premise `value < divisor`. This premise also
excludes a zero divisor. It preserves exact byte lane values through Adler32's
reduction without a signed cast or a change to the Rust implementation.

## Exact operations and definedness

Integer literals, unary negation, addition, subtraction, multiplication,
equality, disequality, and order comparisons are supported. Exact Integer
arithmetic does not overflow. Bitwise operations remain machine operations.

Checked Integer equality rewriting preserves lowering's multiplication by zero
and one identities. These folds only remove expression nodes; other products
retain their shared symbolic structure. Rewritten native observations therefore
keep a checked source spelling for arithmetic certificates, including unsigned
values above the sign bit. See the [identity rewrite regression](https://github.com/clicklang/click/blob/master/mdtests/integer_observed_product_identity_rewrite.md).

Division and remainder are deliberately deferred from the current supported
surface, but their semantics are settled for a future implementation. They use
Euclidean division: for nonzero `d`,

`a == (a / d) * d + a % d` and `0 <= a % d < abs(d)`.

Thus `-7 / 3 == -3` and `-7 % 3 == 2`; this is distinct from C's truncation
toward zero. A zero divisor is a definedness obligation.

Every checked conversion and every future checked division must establish its
definedness in the current proof context before a theorem or execution
certificate is accepted. Evaluation facts are not arbitrary assumptions.

A statement whose evaluation condition is not established where the statement is
written is refused as it is lowered, and the refusal is written for whoever wrote
the statement. It names the clause or expression, the written subterm whose
evaluation raised the condition, and the condition as a requirement in the
reader's own names -- the four bytes at `p[hi - 1]` must be viewable, `hi - 1`
must not overflow, an `Integer` must fit the machine type it is converted back
to. It says how many of that evaluation's conditions the premises did establish
and names them, lists the premises it consulted in source spelling (a premise
that is a conjunction counted as its conjuncts, bounded like every other fact
list), says why a viewability premise over a wider range did not settle a single
cell, and gives one repair: the cell's own viewability as a one-element range,
the operation's `defined(...)`, or the converted value's bounds. Where the
premise set it consulted was empty, it says so rather than implying a premise
was read and rejected. A `.click` clause carries no source span, so the refusal
says that too instead of leaving a reader hunting for a line number.

Logical machine `+`, `-`, `*`, `/`, and `%` at 32 or 64 bits produce one
structural term, with mandatory evaluation-domain obligations beside it.
Known overflow does not erase the term; it leaves an unprovable obligation.
Facts discharge these obligations without changing the term. Operand
promotion and unsigned wrapping retain their C meanings.

Specification `/` and `%` are total
(`eval/operators/spec_arithmetic.rs`, `SpecDivision`). A zero divisor owes
nothing: the term is the kernel's quotient node, which constant folding
leaves standing for a zero divisor (`MachineTerm::divide`,
`MachineIntegerConstant::truncating_div_rem`), so `x / 0` is a fixed but
unspecified value. Only congruence relates it: `a / 0 == a / 0`, and equal
operands give equal quotients, but no rule states a value or a bound for it.
Every rule that bounds a quotient or remainder by a symbolic divisor asks for
a positive or excluded-zero divisor: the difference graph's unsigned
`a % b <= a` and `a - a % b` routes (`DifferenceGraph::nonzero_divisor`),
the interval rules, `operation_bound` (positive constants), the remainder
rewrites, the sign-cast rule, and the `click::integer` division laws, whose
premises name the nonzero divisor. Signed `MIN / -1` and `MIN % -1` still
owe `left != MIN or right != -1`, as the other signed operations owe their
range. `defined(e)` evaluates `e` with C's definedness
(`SpecEvaluation::c_definedness`), so `defined(a / b)` still includes
`b != 0`. Executed C and Rust division keep their undefined-behavior and
panic checks, so the executed term exists only where its divisor is nonzero.
A later decision may add facts about `x / 0` (a chosen value); totality
without one is the weaker, compatible choice
(`mdtests/a_specification_quotient_needs_no_divisor_premise.md`,
`mdtests/a_quotient_by_zero_is_not_zero.md`,
`mdtests/a_remainder_by_zero_is_not_the_dividend.md`,
`mdtests/quotients_by_zero_of_different_dividends_are_not_equal.md`,
`mdtests/a_quotient_by_a_divisor_that_may_be_zero_is_not_bounded.md`,
`mdtests/an_unsigned_remainder_by_a_divisor_that_may_be_zero_is_not_bounded.md`,
`mdtests/a_total_specification_quotient_does_not_define_the_c_division.md`).
Logical shifts also retain a structural value and separate count obligations.
C left shifts retain their signed-value and overflow conditions; Rust shifts
use the original operand width and Rust bit semantics, including wrapping
signed left shifts. Negative counts and counts at least the operand width
remain invalid. The supported 128-bit cases follow the same separation:
signed multiplication, and matching signed or unsigned division and remainder,
retain their range obligations without replacing terms from facts; a zero
divisor owes nothing there either, and the opaque Integer quotient stays
inside its checked conversion.

Capturing such a term as an Integer value retains its domain obligations.
Proof steps discharge them through the ordinary implicit solver and retain
explicit `have` proofs in expansion. A precondition includes its evaluation
domain: callers must prove it, and the callee assumes it on entry. A range
footprint likewise retains the domains of its endpoints. A missing condition
is never dropped. `to_integer(x + 1)` observes a machine sum; mathematical
`to_integer(x) + 1` is total and needs no machine-overflow condition.

A conditional's arm owes its domain only where the condition selects it, as
the right side of `implies` and `or` does: the then arm's obligation `O`
becomes `C implies O` and the else arm's `C or O` (scalar, Integer, and
algebraic `if` alike). An obligation the guard itself states is met. Both arms
are still lowered under the same assumptions, so the guard changes only what
is owed, not the arms' terms. `if s < 64u64 { a << s } else { 0u64 }`
therefore needs no count premise, and a pure function guarded that way is
total and unfolds anywhere; an arm whose guard does not give its domain is
still refused
(`a_conditional_arm_owes_its_domain_only_under_its_guard.md`,
`a_conditional_arm_still_owes_a_domain_its_guard_does_not_give.md`).

## Specification coverage

Integer is supported in:

- specification bindings, typed `let` bindings, and contextual literals;
- universal and existential quantifiers over the unbounded domain;
- pure function parameters and results, and theorem parameters and claims;
- datatype fields and generic type arguments;
- resource model fields and resource pattern bindings;
- typed range-fold accumulators, endpoints, and bodies; and
- mixed C/Integer propositions where every boundary is explicit and checked.

Existing binders, function syntax, match syntax, and fold syntax are reused.
Fold indices and accumulators have independent types: an `int32` index may read
C array elements while an `Integer` accumulator computes an exact sum. Empty
and reversed range behavior is unchanged, and fold initial values and bodies
must have one accumulator carrier.

Quantifier domains remain logically unbounded. Finite enumeration is only a
bounded proof technique. Universal introduction and existential witnesses use
capture-avoiding substitution, preserve carrier identity, and retain any
definedness obligations in the witness or proposition. Deep repeated universal
introduction has a known quadratic cost and is deferred for targeted scaling
work; correctness checks and existing budgets remain in force. See the
[deep quantifier scaling roadmap item](https://github.com/clicklang/click/blob/master/roadmap/deep-quantifier-scaling.md).

For an existential witness, definedness remains attached to that same witness.
It cannot be weakened into an implication whose guard is false, since that
would permit an irrelevant witness to establish the existential claim.
Nor may each domain requirement be put under a separate existential: those
requirements could select different witnesses from the body. Integer,
algebraic, native-integer, and pointer existentials keep each value path's
requirements with its body under one binder. The native conversion regressions
`native_witness_conversion_keeps_its_domain.md` and
`native_witness_conversion_rejects_an_out_of_range_witness.md` check this for
an accepted and an out-of-range selected witness.

Negation selects the dual quantified evidence. `not exists k { P(k) }`
requires every candidate's body to be defined and false; `not forall k { P(k) }`
requires one defined, false counterexample. Undefinedness cannot establish
that a quantified claim is false. Quantifier/negation prefixes select this
binder before lowering the body, preserving obligations at that binder.
The `quantifier_definedness_*.md` tests cover positive, negative, nested, and
undefined-counterexample cases.

## Arithmetic automation and trust boundary

The supported arithmetic automation is linear: addition, subtraction, order,
and multiplication by constants, together with explicit machine-conversion
and checked C-arithmetic laws. Complete symbolic products, truncating quotients
and remainders are opaque affine atoms keyed by exact shared Integer identity.
Linear certificates can add, subtract, scale and compare those values using
explicit premises, without opening their operands or deriving nonlinear laws.
Evaluation guards remain mandatory before a term can enter a proposition or
certificate. There is no promise of general nonlinear automation.

Pure theorem requirements lower in source order. Earlier requirements supply
evaluation evidence for later Integer observations, such as `defined(n + 1)`
before `to_integer(n + 1) == value`. Every requirement remains in the exported
theorem premises, so an application must establish the guards as well as the
observations. Lowering shares the persistent premise context between clauses.


Arithmetic planning emits explicit, inspectable evidence. The kernel validates
operators, coefficients, terms, premises, and range claims independently;
zero-premise tautologies are valid, while sparse or altered premise indices
fail locally. Expansion prints ordinary proof steps, and ordinary verification
rechecks those steps without rerunning the planner. Profiling and audit use the
same checked boundary.

Two rules make the mathematical `Integer` family complete for refutations
over the integers, the form a simplex-based planner produces (see
`design/smt-auto-stage1.md` in the repository). `negated_goal`
assumes the integer negation of a bound goal: for the goal `t <= 0` it is
`-t + 1 <= 0`, and an equality goal is refused. A conclusion node may then be a
contradiction, a constant claim such as `1 <= 0`. This is sound with or
without the negated goal: if the premises and the negation are inconsistent,
the goal holds, and if the premises alone are inconsistent, every goal holds.
`divide` divides a non-strict bound `g*t + k <= 0` by a positive `g` that
divides every coefficient, giving `t + ceil(k / g) <= 0`. Over the integers
this is equivalent to its source, which is the Chvatal-Gomory rounding step
(`mdtests/integer_certificate_refutation_and_rounding.md`). Both are local
node checks charged by bit size, like `scale`.

A bounded nonlinear rule is available explicitly: the `integer_product_bounds`
node in the `rules` arithmetic family consumes four named constant-endpoint
inequalities for the two operands. Multiplication is monotone in each operand
when the other is fixed, with its direction set by that operand's sign; its
extrema on a rectangle therefore occur at the four corners. The kernel checks
those four exact products against the claimed constant lower or upper bound,
including intervals crossing zero. This does not extend the arithmetic planner
or reinterpret a machine product as an exact Integer product. The rule also
checks interval ordering, proposition polarity, references, operand identity,
and the selected conclusion.

Operand comparison uses shared Integer node identities. One node reads exactly
four premises; unused premises and deep operand subtrees do not increase its
checking work. Big-integer multiplication and comparisons are charged from the
numeric bit lengths before arithmetic starts. Deterministic regressions measure
node inventories, unused facts, operand depth, magnitude, and the work-budget
boundary. Pure Integer certificates round-trip and expand/reverify. A synthetic
unchanged C identity wrapper checks a mathematical machine-observer product range
across
verification, expansion/reverification, profiling, and retained audit.

Fold reasoning uses explicit empty-range and next-element laws. Fold terms are
opaque affine atoms in the bounded certificate fragment. The planner accepts
selected checked premises and explicit constant scaling; it does not enumerate
a symbolic range or invent an arithmetic assumption. The unchanged C
summation regression proves exact functional correctness with an `Integer`
prefix sum while separately proving that each machine addition is defined.

Both laws take the raw fold term, which forces a proof to retype the fold at
the proof site. `prove_integer_range_fold_over_equal_terms` restates either law
over a term the caller proves equal to the fold — in practice the opaque
application of the pure function whose declared body *is* that fold. Those
equalities are premises of the produced theorem, beside the law's own guards,
so the entry point assumes nothing the two laws do not already prove. The
append form instantiates the append law at the predecessor index `start..end -
1` and checks, against an empty fact context, that the law's
`fold(start..(end - 1) + 1)` and the caller's `fold(start..end)` are the same
fold by endpoint affine normalization; substituting the caller's term for the
equal shorter fold inside the next-element step is congruence under the second
premise. `integer_range_fold_predecessor_application` builds the predecessor
application so its int32 argument and that index agree by construction.

`substitute_integer_term_in_proposition` is the matching goal refresh. It is
Leibniz for a step that already holds the two terms' proved equality, so it is
deliberately shallow: it descends only the arithmetic spine — negation,
addition, subtraction, multiplication — and compares interned identity
everywhere else, never entering a range fold's binders. Rewriting only some
occurrences of an equal term is sound, and the walk stays linear in the
proposition it rebuilds.

## Sharing, scope, and identity

Integer expressions use immutable shared nodes. A chain of aliases such as
`a0 = x; a1 = a0 + a0; ...` must remain linear in source size rather than
expanding into an exponential arithmetic tree. Canonical nodes have stable,
shallow identities and traversals visit each reachable node once where the
operation permits.

Interning keys contain shallow child identities. Cache maintenance must not
rehash an unrelated large numeral repeatedly or retain dead expression graphs
indefinitely. Alpha keys serialize shared graphs with local child indices.
Renaming and substitution caches include lexical binder scope, and carrier
identities distinguish C values from Integer values.

Substitution and generic rewriting preserve shared arithmetic nodes. They do
not eagerly evaluate newly constant expressions: replacing a variable with a
large repeated-squaring DAG must not allocate an enormous numeral from a tiny
proof. A shared replacement is validated once and its shallow root is charged
at each occurrence.

Memory loads and fold atoms retain exact state identity. Alpha-equivalent
loads from one retained state may match; a different state, body,
carrier, or definedness context does not. Memory state identity is opaque to
arithmetic and is never inferred from a raw term identifier or fingerprint.

Endpoints are the one fold component compared up to equality rather than
identity. A range fold reads nothing but its endpoints, its initial value, and
its body, so two folds with the same initial value and the same body denote
the same Integer once their start endpoints are equal and their end endpoints
are equal. Endpoint equality is decided without any search over the ambient
facts: interner identity, an exact recorded equality between exactly those two
terms, or the two endpoints' affine normal form. The last route is what makes
`(hi - 1) + 1` and `hi` one endpoint, which is how an induction step carries
the append law's `end + 1` back to its goal; wrapping machine arithmetic makes
it exact, so it needs no ordering or definedness side condition. The body
remains exact, so a fold over a written array is never equated with the same
fold over the state before the write.

## Shared machine constants

`MachineIntegerFormat` records signedness and one of the fixed widths 8, 16,
32, 64, or 128. `MachineIntegerConstant` pairs that format with a checked
two's-complement payload; its private fields prevent oversized payloads from
entering a consumer. The inclusive bounds, literal checking, numeric observation,
and conversion policies share this representation. `Bool` is not one of these
formats: it is the logical sort (Stage 5 of `design/machine-integers.md`),
whose integer value at a format is the cast `b as F` (rule C1). Width gives the number of value bytes, not ABI alignment
or a promise that a frontend supports that width.

Checked conversion preserves the numeric value or refuses it. Modulo conversion
is a separately requested operation: it sign-extends a signed source, retains
an unsigned source's value, and reduces modulo the destination width. This
implements the constant policy of C++20 integral conversions and Rust integer
`as`, and of C as GCC and Clang compile it: C source conversions use the
`CConversion` cast mode, which reduces modulo the destination width for
signed destinations too. A specification's casts use the same `CConversion`
mode, and `SpecExpression::Cast` evaluates with the same modular conversion;
`to_T(...)` is the checked conversion.
The ordinary reverse conversion from Integer always uses the checked operation.

The runtime machine types use the shared format for their bounds,
constant observations, Integer conversions, and constant rewrite normalization.
C++ literals use it as well. The runtime bridge requires an exact format match,
including signedness; narrow signed constants retain the
existing sign-extended 32-bit carrier. An arbitrary Integer larger than the
format is refused from its cached bit length before inspecting its limbs.
Parsing work scales with the explicitly written decimal spelling, and numeric
allocation is charged before constructing bounded exact values.

Signed and unsigned 128-bit constants, their full endpoint ranges, widening,
and narrowing are represented and tested against independent exact arithmetic.
The kernel also has a bounded wide scalar profile, described below. Contracts
use `int128` / `uint128` for full-width scalar values. C++ admits the bounded
`__int128` source profile described in the import reference; ordinary C and
Rust source admission remain separate. Reverse conversion arguments supply
Integer context even to negative literals beyond the 64-bit range.

Native signed wide multiplication certifies the equality between its result
observation and the exact Integer product only after both native range guards
hold. Overflow paths carry no result definition. This matches native wide
quotient/remainder result observations and is shared by all kernel clients.
Integer observation keeps unproved path guards and every proof obligation in
its domain, while kernel-certified consequences describe the evaluated value.
Capturing that value therefore requires the guards, without an additional
assumption restating the certified result definition.

## Truncating machine constant division

`MachineIntegerConstant::truncating_div_rem` computes a quotient and remainder
in one already-resolved signed/unsigned 8–128-bit format. It rounds the
quotient toward zero; a nonzero remainder has the dividend's sign, with
`a == b*q + r` and `abs(r) < abs(b)`. This is machine arithmetic, separate
from the planned Euclidean division of mathematical Integer values.

Both results retain the input format. Format mismatch, division by zero, and
signed `MIN / -1` overflow are distinct failures. The overflow also refuses
`MIN % -1`, even though its mathematical remainder is zero. Language
promotions happen before this representation operation; it does not decide
C/C++ undefined behavior or Rust panic policy. Existing signed/unsigned
32/64-bit term construction and recursive constant observations use it while
retaining their execution guards and symbolic nodes. Exact-oracle checks cover
all formats and exhaustive byte pairs; operation batches have deterministic
linear work checks. The symbolic representation is described below; guarded
wide execution and C++ frontend admission are described below. This constant
foundation used artifact schema 38.

## Explicit machine modulo casts

The shared kernel `program_expression::integer_cast_modulo` boundary implements Rust integer `as`
and C++20 integral conversions for the admitted 8–64-bit runtime types. It
checks the evaluated source and destination types, folds root constants through
`MachineIntegerConstant`, and retains symbolic operands in the common term
arena. Its terms come from the one conversion table
(`machine_integer::conversion::lower` and `convert_term`), which C's
conversions use too, so a conversion has one term in every language: a
result of 8 or 16 bits is the generic `Cast` node C builds, printed
`x as uint8` or `x as int8`, and is filed with its destination's range as C's
is, and with nothing else: the identity with its operand is a checked
(specification) narrowing's, filed beside its range obligations. Rule K7 (below) makes its word the operand's low bits, so
`x as uint8 == (x & 255u32)` holds with no fact. Widening uses source
signedness before the destination interpretation. Conversion construction
inspects only a bounded number of root nodes.

A `Bool` source converts to its C1 cast at the destination, 1 when it holds
and 0 otherwise, which owes nothing. A conversion to `bool` is the test
`x != 0`, not this integer boundary. Floats, pointers, arrays, and unsupported
widths are refused here; their ordinary conversions use their own rules. Evaluation
of the operand still carries its definedness obligations, including overflow.
This explicit policy does not relax ordinary C casts or checked Integer
conversions. Casts involving 128-bit values use the generic `Cast`, retaining
both source and destination types. Constants fold through the same exact
format policy, and symbolic operands remain typed through substitution and
proof rewriting. The existing 8–64-bit casts keep their current carriers.

Wide integral widening and narrowing, including signedness changes, are
supported at the kernel's explicit modulo boundary. C conversions involving
wide values are modulo conversions for every destination. A specification's
conversions retain the representable-range policy for signed destinations:
both lower and upper bounds must be established unless the whole source range
fits. Unsigned destinations use modulo conversion.
Neither route loses the operand's definedness obligations.

Exact Integer observation removes a widening cast only when every value of
the source type fits the destination. Narrowing and signedness changes that
can change the numeric value stay machine observations of the converted
value; they are not equated with the source's mathematical Integer.

The `integer_cast_identity` certificate also recognizes the legacy 32/64-bit
conversion terms used by ordinary C and the shared modulo boundary. It compares
the converted observation with the existing typed conversion policy, retaining
the canonical typed-cast check and the two explicit source bounds. Signedness
reinterpretations, signed or unsigned widening, and narrowing still preserve
the numeric value only inside the destination range. This recognition adds no
arithmetic axiom or implicit range fact.

C converts a symbolic `uint64` to `int64` by retaining the same bits with
signed interpretation, for every value and owing no bound, as GCC and Clang
do. Both explicit casts and implicit returns use the same conversion. A
specification's `(int64)` of a `uint64` still owes
`value <= 9223372036854775807u64`.

The complete signed/unsigned 32/64-bit modulo matrix, ordinary C modular
callers, missing bounds, forged endpoint references, false observations and
full-width boundary checks cover this profile. The checked
[cast fixture](https://github.com/clicklang/click/blob/master/mdtests/legacy_integer_cast_identity.md)
includes the unchanged Bitcoin fast-path operand conversion expressions.

## The 32-bit sign cast

A C conversion between `int` and `unsigned int` is the sign cast σ, the
generic `Cast` node from `int32` to `uint32` or back
(`MachineTerm::sign_cast32`). C assignment, return, argument and cast
conversions build it, the usual arithmetic conversions build it for an
`int` operand of an `unsigned` operation, and so does the modulo boundary
above (Rust `as`, C++ conversions, specification casts). A sign-cleared
`unsigned` array index is σ to `int32` (`pointer_index_term`). The
constructor folds a constant and keeps σ of σ as written: `σ(σ(x))` is a
node over σ(x), which the e-graph's R0 puts in `x`'s class.
The widening of an 8- or 16-bit value into `int32` or `uint32` is also
a generic `Cast`, read as its operand's word by rule K8 (below).

σ keeps every bit. From 2026-10-25 the kernel read σ(x) as `x`'s 32-bit
word (rules K1 to K4); step 4b of "Every format its own nodes"
(`design/machine-integers.md`) makes σ a node of its own and deletes K1
and K2, keeping each relation as reasoning:

| Rule | Statement | Where |
|---|---|---|
| K1 word identity | Deleted. σ(x) is a node of its own: no constructor, observation, e-graph or difference-graph reader peels it | the e-graph's R0 (`σ(σ(x))` in `x`'s class) and R-dist (σ of `+ - * & \| ^ ~ <<` is the operator at the other format over σ of the operands; σ of a low word is that low word), `terms/machine_relations.rs` |
| K2 observation | Deleted as a rewrite. `to_integer(σ(x))` keeps σ and reads as `to_integer(x)` at that format, through every σ of a written chain | rule W: `machine_value_reading` |
| K3 orders and indices | Restated. Either 32-bit difference-graph reading of σ(x) is linked to the same reading of `x` with offset 0; an element index reads σ's operand in `int32` index coordinates (decision G1); a sign test of σ is its operand's half-range test; `integer_cast_identity` compares a conversion of a written σ as written | `difference_graph::link_parts`, `structural_interval`, `into_index_word32`, `condition_reasoning/sign_bit.rs`, `conversion::cast` |
| K4 modular equality | Restated: an observation of σ(x) reads `x` | through rule W |
| K6 equality | A lookup-level equivalence: a 32-bit equality is a term of its written format; its identity and keys read it at `int32`, each side through one σ | `comparison_identity`, `condition_match_key` |
| C quotient | σ of a quotient or remainder on a nonnegative dividend and a positive divisor is the quotient or remainder at the other signedness of σ of its operands | `condition_reasoning/sign_cast_division.rs`, `nonnegative_division_bound_guards` |

Soundness: σ_{S→F}(x) is `to_integer_S(x) mod 2^32` read in `F`. Reducing
modulo 2^32 and reading two's complement are inverse bijections between
either format's range and the 32-bit words, so `bits(σ(x)) = bits(x)`, and
σ_{F→S}(σ_{S→F}(x)) = x (R0). A sign-free operator computes its result's
bits from its operands' bits alone, so σ distributes over it (R-dist). An
equality compares bits, so it reads through σ (K6). For rule C, `0 <= A <
2^31` and `0 < B < 2^31` have the same value in both formats, truncating
and unsigned division agree on such values, and the quotient and remainder
lie in `[0, A]`, which both formats hold.

A term keeps σ as its source wrote it: printed facts and steps show
`(x as uint32)` or `(x as int32)` wherever σ is, inside operators and
comparisons too. An `int32` order of a `uint32` value is spelled with the
operand converted: the case condition the implicit tail synthesizes for
`bool set = (int)u < 0;` is `u as int32 < 0`, which lowers back to that
order, where the bare `u < 0` would be the `uint32` order
(`surface_synthesis::bitvector_spells_uint32`,
`mdtests/execute_splits_a_sign_cast_order_as_a_signed_comparison.md`,
`rust_execute_splits_a_sign_cast_order_as_a_signed_comparison` in
`tests/rust_import.rs`).

A 32-bit load carries its signedness, `LoadKind::Int32` or
`LoadKind::UInt32`, taken from the lvalue's type in every front end (C, C++
and Rust lower a read to a typed load of the source type). Rule K5
(2026-10-25): a typed read at signedness F of a cell holding a value stored
at the other signedness S returns σ_{S→F} of the stored word
(`ProgramType::read_cell`), so `4294967295u` stored and read through `int *` is
`-1` (`mdtests/a_32_bit_cell_read_at_the_other_signedness_is_its_sign_cast.md`,
`mdtests/cpp_an_unsigned_cell_read_as_int_is_its_sign_cast.md`,
`rust_a_u32_cell_read_as_i32_is_its_sign_cast` in `tests/rust_import.rs`).
Soundness: the read returns the same four bytes in F, which is the modular
conversion. Each read is its own load: a `UInt32` read has a load variable
of its own, defined by its own read (`load_variable_for_term`,
`mint_load_variable_identity`). The equality graph relates the two reads of
one cell by σ (R-mem): the `int32` read is the cell's word load
application, and the `uint32` read is σ of it; an `int32` read of a cell
storing a `uint32` value is σ of that value. Kernel-internal reads (index
arithmetic, pointer words) are `Int32`.

A constant has a format: `MachineTerm::Constant { format, bits }` is
one node for every format (decision G9), built by
`MachineTerm::constant(v)` at `int32`, the format of every
kernel-internal constant, `uint32_constant`, `int64_constant`,
`uint64_constant` and `machine_constant`. A C, C++ or Rust value at
`uint32` takes the `uint32` format: literals,
`MachineIntegerType::constant_term` and every conversion that folds to
`uint32`, `kernel::uint32` and `value_from_term`
(`MachineTerm::in_format32`). Inside an `int32` operator, comparison or
overflow test a `uint32` constant is read as the `int32` constant of its
bits (`into_word32`, `constant_word32`), and the e-graph interns both as
one atom (`MachineAtom::int32`). The difference graph reads its value, and
the kernel's matches on a 32-bit constant's bits read either format
(`constant32`, `as_const`, or `bits32_constant!`). A formatted constant prints in its own type
(`4000000000u32`, not `-294967296`) wherever a renderer reaches it
(`mdtests/a_uint32_constant_above_int32_max_is_stated_stored_and_read_as_itself.md`,
`mdtests/cpp_a_uint32_constant_above_int32_max_is_stored_and_read_as_itself.md`,
`rust_a_u32_constant_above_i32_max_is_stated_stored_and_read_as_itself` in
`tests/rust_import.rs`).

A 32-bit equality is one fact at either signedness (rule K6, restated as a
lookup-level equivalence by step 4b). An equality of `uint32` values is a
`Compare { UInt32, Equal }` term over its `uint32` operands
(`ConditionTerm::uint32_equal`), and prints in its own type
(`old(u[0]) == 4294967295u32`, not `== -1`); no rewrite re-files it at
`int32`. `ConditionTerm` and `BitvectorComparisonOp` compare, hash and
order it as the `int32` equality of the same bits: `comparison_identity`
reads each side through one σ and a constant of either spelling as its
bits, one match per side with no clone, and `condition_match_key` and the
structural fact keys read the same form, so every fact index, key and
lookup finds it at either format, and it is never filed twice
(`mdtests/a_uint32_equality_above_int32_max_is_one_fact_with_its_int32_word.md`,
`a_32_bit_equality_is_one_fact_at_either_signedness`,
`rust_a_u32_equality_above_i32_max_is_stated_used_and_printed_as_itself`).

Rule C (decision of 2026-11-02): σ of a 32-bit quotient or remainder is the
quotient or remainder at the other signedness of σ of its operands, when
the dividend's `int32` reading is nonnegative and the divisor's positive.
It is read where a comparison naming σ of a quotient is decided
(`decide_by_sign_cast_division`, after the sign-bit rule) and filed beside
such a fact when it is assumed, one match on each side's root and two sign
decisions per side; the quotient bound guards of `normalize using` read
it too (`nonnegative_division_bound_guards`)
(`mdtests/a_sign_cast_of_a_nonnegative_quotient_is_the_quotient_at_the_other_signedness.md`
and its refusal,
`mdtests/a_sign_cast_of_a_quotient_with_a_dividend_of_unknown_sign_is_not_the_other_quotient.md`,
`mdtests/machine_quotient_remainder_bounds.md`).

## The word of a narrow cast

Every conversion into an 8- or 16-bit format, in C, C++, Rust or a
specification, is a generic `Cast` node (the conversion table's `Cast`
entry). Rule K7 (decision of 2026-10-26) gives its 32-bit word: for a
destination of `b` bits, `m = 2^b - 1` and `s = 2^(b-1)`, and `w` the
operand's word (its low word, the `UInt32From64` spelling of `Cast`, for a
64-bit operand),

| Destination | Word of `Cast(S -> F, x)` |
|---|---|
| unsigned (`uint8`, `uint16`) | `w & m` |
| signed (`int8`, `int16`) | `((w & m) ^ s) - s` |

Soundness: the cast denotes `n mod 2^b` read in `F`, whose word is the zero
or sign extension of those bits (`docs/internals/kernel.md`, "One meaning
for a narrow value"). `w` holds `n mod 2^32`, so its low `b` bits are
`n mod 2^b`; the mask zero-extends them, and for `t` those bits `(t ^ s) -
s` is `t` below `s` and `t - 2^b` from `s`, without a 32-bit wrap: their
sign extension. The e-graph holds the identity: interning a narrow cast
puts it in one class with that word, built from the operand's class, so a
written mask of the operand, or of an equal word, meets the cast with no
fact (`examples/integer-languages`, `narrow_u8`). The work is constant per
cast. Inside the destination range the cast also equals its operand
(`narrowed_cast_identity`), and `integer_cast_identity` reads it as a cast,
so `x as i8` in Rust verifies the in-range identity as C's
`(signed char)x` does.

## The widening of a narrow value

Integer promotion, the usual arithmetic conversions, and every widening
assignment, return, argument or cast of an 8- or 16-bit value into `int32`
or `uint32` build the conversion table's `Cast` in C, C++ and Rust (Rust's
`From` included). Rule K8 (decision of 2026-10-26): the 32-bit word of
`Cast(S -> F, v)`, `S` narrow and `F` of 32 bits, is `v`'s word. The
widening is a node of its own, related to `v` by value (K8 as a relation,
step 6); no constructor peels it. A widening into 64 bits is the legacy
extension of that word.

Soundness: by the narrow-value invariant `v`'s word is the sign or zero
extension of its value `n` to 32 bits, and `n` fits `F` (or, for a signed
`n` into `uint32`, `n mod 2^32` has the same 32 bits), so the conversion's
word is `v`'s.

`integer_cast_identity` reads a widening by that word only through its
narrow-widening check, which requires a canonical carrier or a binder's
stated range (`conversion::narrow_widening`), never by the bare word
comparison it uses for σ: a word merely tagged narrow is not promoted. A
checked narrowing of a widened value is the narrowing of `v` from `v`'s
format, and files its identity as before. A promoted narrow value at rest
prints as `c as int32` or `c as uint32`, as σ does; inside an operation it
prints as `c`.

## Wide runtime scalars


The shared kernel has `ProgramType::Int128` / `UInt128` and corresponding `ProgramValue`
wrappers in the existing machine-term arena. `program_expression::int128_literal` and
`program_expression::uint128_literal` retain all 128 bits in `MachineIntegerConstant` payloads.
Symbolic variables, scalar locals, assignment, function parameters/results,
and substitution preserve the wide type. The pinned x86_64 Linux profile gives
these scalar objects 16 bytes and alignment 16; value width alone does not
choose an arbitrary target's ABI alignment.

Exact Integer observation retains the source's wide machine type and numeric
interpretation. Reverse Integer conversions use the full signed/unsigned
bounds and retain both obligations for symbolic inputs. Truthiness compares
that exact observation with zero, including high bits above bit 63. These
observations do not turn native arithmetic into unbounded Integer arithmetic.

A wide runtime wrapper accepts only a matching wide constant, a symbolic
variable, a matching typed memory load, the shared checked Integer-to-machine
node, or a typed machine cast for that destination.
Legacy word constants and arithmetic nodes cannot acquire 128-bit semantics
by retagging their wrapper. Validation examines the root and any strictly
widening conversion chain (bounded by the five machine widths); substitutions,
alpha keys, state identities, and bounded walks keep the full payload.

Signed native 128-bit multiplication observes each integral operand exactly,
computes its Integer product, and checks both signed 128-bit bounds. Unknown
bounds retain separate normal and signed-overflow paths; known failed bounds
produce signed overflow. The normal symbolic result uses the shared checked
Integer-to-machine node, retaining its machine type rather than erasing it to
an Integer. Existing product-bounds certificates can discharge these guards.
At least one operand must already be signed 128-bit; a later widening cast
cannot rescue overflow in an earlier narrow multiplication. Operand undefined
behavior and proof obligations remain attached to the result.

Exact typed 16-byte cells support signed and unsigned wide stores and loads
through the existing typed-lvalue operations. Symbolic loads use the shared
state/address/kind identity and certified defining facts. Their kinds retain
signedness to match the checked constant format; cross-type reinterpretation
and byte views remain unsupported. A wide read or write requires the full
16-byte extent and resource authority, and retains initialization obligations.
Framing and store invalidation account for every byte, including bytes 8–15.
The conservative fallback width for an access of unknown type is now 16;
indexed store-gap decisions use the same bound. Known load kinds, pointer
reads, and retained typed cells use their own access widths; a wider unknown
fallback must not erase precise separation evidence.

The shared runtime and internal Click's C type identities also model signed and
unsigned wide object pointers, pointer slots, fixed scalar arrays, and arrays
of those pointers. Scalar array elements and pointer arithmetic use a 16-byte
stride; pointer objects and pointer-array slots retain the LP64 8-byte width.
Address-of preserves the exact pointee type. Automatic array elements retain
initialization requirements, one-past pointers cannot be dereferenced, and
pointer-slot authority does not grant authority over the pointee. Static array
startup preserves full-width initializers; ordinary function entry declares
the storage without contents, restoring no initializer and granting no
resource. A read of an untouched element is one load at function entry, so
entry and a selected read do not visit unrelated elements. Compact scalar-copy checks include a wide
cell overlapping the region's prefix.

Other native wide arithmetic, including unsigned wrapping multiplication,
source aggregate layouts, byte views of wide cells, and callbacks remain
unsupported. C++ now admits wide scalar locals, parameters, results,
matching-width call captures, modulo integral casts, Boolean conversions, and
checked signed multiplication, division/remainder, and comparisons. Contracts
observe these values through `to_integer` and use checked reverse conversions.
Wide source pointers, references, arrays, and record fields
remain unsupported, as do ordinary C and Rust wide source spellings. Internal
C identities model the wider memory profile without granting source admission.

## Work budgets and certificate scaling

Numeric work has two independent costs: reachable expression visits and
magnitude-dependent arithmetic work, including numeric bit length. A numeric
operation consumes the active verification budget before doing the operation.
Lowering also checks the configured simple-operation allowance. A counter added
after arithmetic is insufficient, and a weighted charge must not be simulated
by a loop of unit checkpoints.

Shared DAG traversals, substitution, alpha comparison, certificate checking,
and state matching must scale with the selected expression and certificate,
not unrelated proof state. Premise references are explicit and checked before
storage allocation. Large constants do not silently truncate, and enormous
mathematical ranges do not trigger uncontrolled enumeration.

The trust boundary is independent kernel checking of the resulting proof
object and certificate. C source remains the verification boundary: the
unchanged summation program is the regression, and proof authors must not add
no-op C branches, proof-only locals, helper rerouting, or renamed identifiers
to make an Integer proof succeed.

## Related references

- [Kernel implementation](kernel.md)
- [Verification efficiency](verification-efficiency.md)
- [Memory derivation DAG](memory-dag.md)
- [Language reference: mathematical integers](../reference/language/index.md#mathematical-integers)
- [Canonical unchanged-C summation regression](https://github.com/clicklang/click/blob/master/mdtests/integer_sum_range_fold.md)
- [Missing element-bound regression](https://github.com/clicklang/click/blob/master/mdtests/integer_sum_range_fold_missing_bounds.md)
- [Intermediate-overflow regression](https://github.com/clicklang/click/blob/master/mdtests/integer_sum_range_fold_intermediate_overflow.md)
- [Endpoint congruence regression](https://github.com/clicklang/click/blob/master/mdtests/fold_endpoints_rewrite_under_equality.md)
- [Endpoint congruence refusal](https://github.com/clicklang/click/blob/master/mdtests/fold_endpoints_reject_a_different_body.md)

## Symbolic truncating quotient and remainder

The shared Integer DAG has explicit `TruncatingQuotient` and
`TruncatingRemainder` nodes for the native machine arithmetic foundation.
These internal nodes are distinct from the planned Euclidean Integer `/` and
`%` surface operators. Nonzero root constants fold exactly, with a quotient
truncated toward zero and a remainder carrying the dividend's sign. The
representation is unbounded, so signed machine MIN/-1 overflow belongs to the
native execution guard, rather than the mathematical term constructor.

A zero divisor stays opaque. Constructors do not cancel `x/x` or `0/x`;
these nodes do not certify a native division's definedness. Native execution
must establish nonzero divisors and the signed overflow exclusion before
producing results. Proof spellings and C++ source admission build on this
representation as described below.

Interning, alpha keys, variable collectors, binder-aware rewriting, fold
framing, and diagnostics preserve the distinct operators. The affine solver
conservatively refuses symbolic truncation. Arithmetic-spine proposition
substitution memoizes shared nodes and rebuilds both operands; substituting
nonzero constants folds, while substituting a zero divisor stays opaque.
Regressions cover full-width signed/unsigned magnitudes, both remainder signs,
2/8/32/128-node shared DAGs, and explicit numeric bit-length work charging.
This representation foundation used schema 38 without admitting new source operations.

## Integer conditional

`IntegerTerm::If { condition, then_term, else_term }` is the Integer
counterpart of the machine `MachineTerm::If`: a `ConditionTerm` and two
shared (`SharedIntegerTerm`) arms. `IntegerTerm::if_then_else` builds it and
leaves one arm for a constant condition or equal arms, so neither stands.
`SpecIntegerExpression::If` holds the written proposition and Integer
branches; evaluation lowers it as a scalar `if` is lowered: a literally
constant condition selects its branch, and any other lowers both into one
conditional term (`evaluate_spec_integer_if_paths_in`). Lowering reads no
ambient fact, so choosing a branch is a proof step.

The term has the machine conditional's capabilities and no more. Its shallow
interning key is its condition and its arms' ids. Substitution, variable
collectors, alpha keys, memory-load and resource-read collectors, narrow
carrier and fold-read checks, and both printers walk the condition and the
arms; the Surface spelling is `if c { a } else { b }`. A rewrite that decides
the condition (a substitution, `normalize() using`, or `solve`'s known
conditions) leaves the selected arm, and arms a rewrite makes equal leave one,
also under an exact Integer substitution, since that only deletes a node:
`rewrite(x, y); normalize();` closes `(if c { x } else { y }) == x`, as for
a machine conditional. The affine fragment keeps an unresolved conditional as
one opaque atom by its shared identity, as it keeps a product or quotient; a
bound over its arms takes a case split
(`mdtests/an_integer_if_in_a_theorem_verifies.md`,
`mdtests/an_integer_if_is_reduced_under_a_known_condition.md`,
`mdtests/an_integer_function_with_an_if_body_unfolds.md`). A termination
measure may not read one, as it may not read a machine conditional.

## Guarded wide native division

Kernel execution admits quotient and remainder on matching `Int128` or
`UInt128` values. Callers must resolve promotions before this boundary.
Execution checks the divisor's full-width Integer observation against zero.
Signed execution additionally excludes `MIN/-1` for both `/` and `%`, using
`left != MIN || right != -1` in the existing proposition model. Each unknown
guard retains a UB path and a guarded normal path; proving nonzero alone does
not eliminate signed overflow, and proving the overflow exclusion alone does
not eliminate division by zero. Known operand conditions simplify the guard.

After these guards, the shared mathematical quotient/remainder fits the
result's native format. Constants preserve their signedness and all 128 bits;
symbolic results use the checked Integer-to-machine representation. Only the
normal path carries the kernel-certified equation equating its full-width
machine observation with that mathematical term. This equation follows from
the native operation, rather than an assumed conversion range. Operand
execution obligations are preserved before either operation.

Exact guard lookup does not scan unrelated ambient facts. Regressions cover
signed/unsigned extrema, quotient and remainder signs, zero and MIN/-1,
missing guards, explicit promotions, checked function artifact rechecking, and
2/8/32/128-operation work scaling. Equality-as-false and inequality-as-true
guards use exact indexed lookup, including the signed overflow disjunction.
C++ source division/remainder is admitted in schema 39; wide source memory
remains separate work. See the [C++ import profile](../reference/cli/import.md).


## Explicit truncation in proofs

`truncating_quotient(a, b)` and `truncating_remainder(a, b)` take two
mathematical Integer arguments. Quotients truncate toward zero; a nonzero
remainder has the dividend's sign. Both require `b != 0`, including under
cancellation or multiplication by zero. Native operand evaluation retains its
own definedness obligations: `truncating_quotient(to_integer(x + 1), 3)` also
requires the machine addition to be defined.

Nonzero constants fold exactly at arbitrary width. Mathematical `MIN/-1`
therefore denotes the positive unbounded quotient; it does not establish that
a native signed division is defined. Symbolic terms remain opaque to affine
reasoning. These explicit spellings leave mathematical Integer `/` and `%`
unavailable, preserving their separate planned Euclidean policy.

<!-- verified-example: mdtests/integer_truncation.md -->
```click
theorem guarded(a: Integer, b: Integer) {
    requires b != 0;
    ensures truncating_quotient(a, b) == truncating_quotient(a, b) by solve();
    ensures truncating_remainder(a, b) == truncating_remainder(a, b) by solve();
}
```

The kernel retains deferred operands and mandatory domain obligations before
constructing shared terms. A pure expression with a nonzero constant divisor
can use the shared Integer DAG directly. Deferred truncation is not treated
as an obligation-free argument or a total fold summary. Expansion preserves
the spellings and verifies again; regressions check hostile constants, erased
guards, full-width signs, native operand obligations, shared aliases, and
lookup with unrelated facts. The proof notation has mathematical Integer
semantics; C++ source division/remainder separately retains native guards and
uses artifact schema 45.


The shared library now exposes `integer::truncation_identity` under `d != 0`,
relating the symbolic terms by `n == truncating_quotient(n, d) * d +
truncating_remainder(n, d)`. For positive `d`, retaining the nonzero domain
premise,
`integer::positive_divisor_remainder_lower` and
`integer::positive_divisor_remainder_upper` establish `1 - d <= r <= d - 1`.
`integer::nonnegative_dividend_remainder` and
`integer::nonpositive_dividend_remainder` establish the corresponding remainder
sign under a nonzero divisor and the explicit dividend sign premise. Negative
divisors are supported by the identity and sign laws. These are kernel laws of
the builtin Integer operations; reserved declarations are checked against their
exact parameter types, guards and conclusions. They establish no native
operation or narrowing safety. General affine reasoning still does not open
symbolic truncation or derive identities between distinct symbolic products.
Their complete values can participate as opaque affine atoms.

<!-- verified-example: mdtests/integer_truncation_laws.md -->
```click
theorem check_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d) by {
        apply(integer::truncation_identity(n, d));
    }
}
```


## Capturing native observations as theorem arguments

An Integer theorem parameter can receive a fixed-state native observation such
as `to_integer(x + 1)`. The argument denotes the Integer value captured at the
application site, and its native evaluation must be defined there, even when
the theorem's conclusion is reflexive. Entry, marked and returned values retain
the state named by their source expression. Capturing the expression reads only
its explicitly referenced bindings; it does not enumerate other locals or
copy the proof history.

Smart `apply` proposes source evidence for argument evaluation as well as the
callee's declared requirements. It rechecks capture using only that proposed
evidence before emitting a simple `apply ... using` certificate. Removing a
required guard makes expansion/reverification fail. A guard without a supported
source spelling produces a bounded search refusal; explicit `using` evidence
can supply it. Capturing an observation supplies no native range or narrowing
identity automatically.

<!-- verified-example: mdtests/integer_theorem_observed_arguments.md -->
```click
theorem integer_reflexive(z: Integer) {
    ensures z == z by solve();
}

theorem observe64(x: int64) {
    requires defined(x + 1i64);
    ensures to_integer(x + 1i64) == to_integer(x + 1i64) by {
        apply(integer_reflexive(to_integer(x + 1i64)));
    }
}
```


## Full-width native comparisons

All six native comparisons accept matching `Int128` or `UInt128` operands.
Promotions remain caller-owned. A shared condition constructor observes both
operands as mathematical Integers with their native signedness, then builds
an Integer equality, disequality, or ordering node. Execution and pure-spec
branch transport use this same constructor, so retained source branch proofs
keep the full relation rather than narrowing it to a legacy word predicate.

Known conditions produce an `Int32` zero or one; unknown conditions retain
both outcomes with their exact true/false guards. Complementary relations
have distinct Integer nodes, so execution queries at most two indexed keys
(the requested relation and its complement). It does not scan unrelated
premises or assume new facts. Operand runtime errors and undefined behavior
are preserved before evaluating the comparison.

Regressions compare all six operations against a full-width ordering oracle,
including signed MIN/MAX, unsigned MAX, and values above 64 bits. They cover
true/false and complementary premises, explicit conversions, hostile operand
arithmetic, constant work over growing ambient fact populations, and linear
work over growing explicit operation counts. C++ schema 45 admits these
comparisons and requires refreshing older source locks; ordinary C and Rust
frontend admission remains separate. Source verification, expansion, offline
artifacts, and retained audit use the shared kernel behavior.


## Truncating division bounds

The explicit `integer_division_bounds` node in the `rules` arithmetic family
checks a non-strict constant bound on `truncating_quotient(n, d)` or
`truncating_remainder(n, d)`. Four named premises supply constant-endpoint
numerator lower/upper and divisor lower/upper bounds, in that order. Both
intervals must be ordered, and the divisor interval must exclude zero. Positive
and negative divisor intervals are supported; an interval crossing zero is
refused even when another ambient fact says the divisor is nonzero.

Quotient extrema are the four corner quotients, computed with truncation toward
zero. Remainder bounds use the largest divisor magnitude minus one, narrowed by
the numerator's magnitude and sign. These remainder bounds are conservative.
When every numerator magnitude is strictly below every divisor magnitude, the
remainder equals the numerator and its input interval is retained exactly.

The checker reads only its four named premises and uses shared Integer operand
identities. It validates polarity, endpoints, operand correspondence, references,
and the selected conclusion. Magnitude-dependent work is charged before
arbitrary-precision division. Regressions compare signed small-value oracles,
large bounds, false claims, zero-crossing and inverted ranges, malformed
certificates, unused premise populations, certificate node counts, and exact
work-budget boundaries.

The companion `integer_relation_transport bounds [i, j] => P` node names an
Integer equality followed by either an Integer equality or a non-strict bound.
It replaces exactly one whole operand of the second relation by its equal;
equality orientation may be reversed, but relation kind and truth polarity are
preserved. It does not rewrite inside an expression, search ambient facts, or
reinterpret a nonlinear term as affine arithmetic. Its checking work is constant
per node and independent of unused premises. This supplies explicit composition
from a native operation observation to its mathematical bound, and then from a
range-checked cast observation to the exact quotient/remainder result.

Expression lowering still requires the operation's nonzero guard in scope.
A numeric interval does not silently supply that evaluation guard. The fixture
states it explicitly, while the division-bound checker separately validates that
its own divisor interval excludes zero.

This is a mathematical truncating-division rule, separate from the planned
Euclidean division laws. It supplies no implicit machine observer ranges and
proves no native definedness or cast identity. Compose it with the existing
native division guards, exact quotient/remainder observations, and
`integer_cast_identity` for range-checked narrowing. See the checked
[division-bound fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_division_bounds.md).


## Observing defined signed 64-bit operations

`integer::int64_subtract_to_integer` extends the signed int32 observation laws to the
full signed 64-bit carrier. Like the int32 laws, it is a proved library
theorem: its pinned proof turns `defined(left - right)` into the Integer range
of the difference and applies the `integer_operation_identity` certificate
rule. The exact observation requires the native `defined(left - right)` fact.
Modular machine terms alone do not establish mathematical subtraction, and an
overflow case cannot discharge the guard. Declaration checks retain the signed
width, operation, guard polarity and exact conclusion. The in-range addition
identity `to_integer(left + right) == to_integer(left) + to_integer(right)`
needs no library law: `solve()` proves it from `defined(left + right)`.

The unchanged Bitcoin division sidecar states that addition identity as a
`have` with its proof omitted for the three possible correction
values after proving each native sum is defined. Explicit Integer arithmetic then bounds those corrected observations
before the original short-circuit expression executes. Signed order reflection
restores native bounds on the actual returned value. This proves output bounds
for both rounding branches; identifying the result as a mathematical
floor/ceiling remains separate. Missing and false guards, expansion,
reverification and deterministic application scaling cover the subtraction
law.
See the checked
[operation fixture](https://github.com/clicklang/click/blob/master/mdtests/int64_integer_operation_bridges.md).


## Exact unsigned 64-bit observations

The shared `uint64` observation bridges preserve unsigned semantics, including
values above `INT64_MAX`. Their premise is explicit; `defined(a + b)` alone
cannot exclude unsigned wrapping.

| Standard theorem | Required premise | Exact observation |
| --- | --- | --- |
| `integer::uint64_add_to_integer` | `A + B <= UINT64_MAX` | `to_integer(a + b) == A + B` |
| `integer::uint64_multiply_to_integer` | `A * B <= UINT64_MAX` | `to_integer(a * b) == A * B` |
| `integer::uint64_subtract_to_integer` | `B <= A` | `to_integer(a - b) == A - B` |
| `integer::uint64_divide_to_integer` | `b != 0u64 and B != 0` | `to_integer(a / b) == truncating_quotient(A, B)` |
| `integer::uint64_remainder_to_integer` | `b != 0u64 and B != 0` | `to_integer(a % b) == truncating_remainder(A, B)` |
| `integer::uint64_to_integer_less_equal_implies_less_equal` | `A <= B` | `a <= b` |

Here `A = to_integer(a)`, `B = to_integer(b)` and
`UINT64_MAX = 18446744073709551615`. The divide and remainder laws
are kernel standard theorems with checked parameter types, declaration shape,
exact premise and conclusion. The add, multiply and subtract laws are proved:
their pinned proofs derive the Integer range of the exact result from the
premise and the operand ranges (`integer_product_bounds` for the product's
lower bound) and apply the `integer_operation_identity` certificate rule. The order law is proved by `known()`: a
machine comparison and the Integer comparison of its operands' observations
lower to one fact, so its conclusion is its premise. The forward
direction needs no lemma: `known()` or `solve` reads `a <= b` as
`A <= B` directly.
These laws use the same observation model and theorem application path as the
existing uint32 and signed bridges, without changing source-language arithmetic. Division states both the native
and observed nonzero facts so the machine operation and mathematical
truncation each have an explicit evaluation domain. The bridge does not
infer either domain from the other.
They apply to the shared machine model used by C, C++ and Rust.

Boundary models cover zero, the sign bit, UINT64_MAX, wrapping and the Bitcoin
fast-path operand limits. Regressions reject forged declarations, omitted or
weakened guards, wrong widths and signed carriers. Ordinary C functions and
modular callers verify all five operation laws; expansion reverifies, and
explicit order-bridge applications retain deterministic scaling. See the checked
[unsigned fixture](https://github.com/clicklang/click/blob/master/mdtests/unsigned_integer_bridges.md).


## Restoring signed native facts

Signed `int32` and `int64` observations preserve and reflect non-strict order.
The standard-library `integer::int32_to_integer_less_equal_implies_less_equal` and
`integer::int64_to_integer_less_equal_implies_less_equal` lemmas restore native order from an exact
Integer comparison. The forward direction, and injectivity at `int64`, need no
lemma: the machine comparison and the Integer comparison of the observations
lower to one fact, so `known()` or `solve` reads one as the other.
`integer::uint32_to_integer_equal_implies_equal` is an injectivity bridge for the unsigned
32-bit carrier: equal pattern bits do not depend on signedness, and every
pattern has one unsigned Integer value.

These are width-specific library theorems proved by `known()`: the
native comparison and the Integer comparison of the observations lower to one
fact. They require no overflow fact because an already-existing bit pattern
has one exact Integer value.
They infer neither implicit ranges nor narrowing identities. Prove the cast
identity and transport its Integer bounds before applying the reverse order
bridge to the narrowed native result. The C++ regression uses a range strictly
smaller than either native carrier, retains expansion/reverification and audit,
and frames unrelated memory through a modular caller.

Regressions refuse missing or reversed premises, wrong carriers, false native
bounds, and incorrect certificate references. See the checked
[signed bridge fixture](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).


## Bounds excluding constants

The explicit `integer_bound_exclusion bounds [i] => P` `rules` certificate
excludes a constant strictly outside one named non-strict Integer bound. From
`lo <= x` it can establish `x != c` when `c < lo`; from `x <= hi` it can
establish `x != c` when `hi < c`. Equality at the endpoint is refused. The
result may reverse the disequality operands; a false equality has the same
meaning, while a true equality or false disequality is refused.

The checker reads one premise and compares shared Integer operand identities.
It accepts nonlinear operands without collecting affine terms. Endpoint and
excluded-constant comparison work is charged from their bit lengths before the
comparison. Unused facts do not change checking work, and certificate checking
scales linearly with its node count. This rule supplies no implicit machine
range or evaluation guard.

For a positive `int32` divisor, first prove `1 <= d` and use the existing
`integer::int32_less_equal_to_integer` bridge. Excluding `0` and `-1` from
`1 <= to_integer(d)` then proves the wide signed division guards without adding
them to the contract. See the checked
[bound-exclusion fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_bound_exclusion.md).


## Range-checked modulo cast identities

The explicit `integer_cast_identity` node in the `rules` arithmetic certificate
family proves that a typed modulo cast preserves its mathematical value.
Its result equates the cast's full-width Integer observation with the exact
source observation, in either direction. Two named premises must have the
forms `lo <= source` and `source <= hi`, with constant endpoints in that order.
The kernel checks that the interval is ordered and entirely inside the
cast destination's signed or unsigned range. Stronger intervals are allowed.

The rule checks the cast's source and destination metadata, operand format,
observation type, proposition polarity, referenced premises, and selected
conclusion. It reads only the two named premises. Integer node identities
avoid ambient searches, and endpoint comparisons charge numeric bit lengths.
Regressions check boundary modulo oracles, forged formats and payloads,
missing or altered bounds, unrelated equality claims, constant checking work
with growing unused premise populations, and linear work with certificate nodes.

The Integer-to-machine conversion is a conversion too: `to_integer(to_T(z))
== z`, either side first, from `lo <= z` and `z <= hi` inside `T`'s range,
at every format, 128 bits included (`conversion::integer_conversion`, one
match on the observation's root). `to_T(z)` denotes an element of `T` that
is `z` whenever `z` lies in `T`, and its lowering owes `z`'s range wherever
it appears, so the rule states that meaning and nothing more. `solve` plans
it as it plans a cast's identity, spelling `z` as the operand the
observation writes, and the eight library `to_*_round_trip` laws are proved
by it
(`mdtests/an_integer_converted_to_a_machine_type_reads_back.md`).

Nested conversions are compared with the canonical modulo cast of the source
observation, including a narrowing cast that discards an intermediate cast.
Unsigned byte readback also admits an exact low-bit mask: a `uint32` source
masked by `255` for a `uint8` observation or `65535` for a `uint16` observation.
Both forms require the same two range bounds. A narrow observation of the
source's 32-bit carrier, or of the low word of a 64-bit source, is admitted
too, again with bounds on the source observation inside the destination
range; every narrowing the kernel produces is a conversion node, so such an
observation arises only from a word already known to lie in the range. A
widening of an 8- or 16-bit value into a type that contains it is admitted
when the observation reads the same word, or its 32-to-64-bit sign
extension (zero extension for an unsigned source); the word is the value's
canonical carrier, so the source's own range serves as the two bounds. C's narrowing into those types is a typed
generic `Cast` node; the rule compares it with the canonical cast, and
also looks through a C conversion from a 32-bit type that contains the
destination (`w as int32 as uint16`) to the carrier beneath it, under the same
bounds. A different mask, operand, or destination is refused; widening after an intervening truncation cannot be
mistaken for a direct cast of the original value. These forms connect native
Rust narrowing stores to their full-width modulo results.

This is a shared proof rule, not a change to C++ conversion semantics or an
automatic range inference rule. Outside the destination range, native modulo
casts remain defined and may change the mathematical value. Proof-side checked
conversions retain their existing range obligations; C conversions owe none. The certificate does not establish that its source arithmetic is
defined: observing a native quotient or remainder still requires its nonzero
and signed overflow guards.

C++ regressions cover signed/unsigned 128-bit values narrowed to signed/unsigned
32/64-bit values, explicit casts and implicit returns, guarded native quotient
and remainder narrowing, modular caller framing, offline artifacts, expansion,
and retained audit. The source profile remains unchanged; the current artifact schema is 45.


## In-range machine sums, differences and products

The `integer_operation_identity` node in the `rules` family proves that a
machine `+`, `-` or `*` that does not wrap is the same operation on its
operands' Integer values: `to_integer(a + b) == to_integer(a) +
to_integer(b)`, or with `-` or `*`, in either orientation. The operation is
of any format of 8 to 64 bits (`int`, `unsigned int`, `int64`, `uint64`, and
the narrow formats, whose operations are the 32-bit word's), and each operand
is observed in that same format. Two named premises `lo <= S` and `S <= hi`
bound the stated Integer result `S` by constants inside the format's range,
in that order. The kernel recomputes `S` from the observed operation
(`kernel::machine_integer::identity::mathematical`) and reads only the two
named premises (`mdtests/an_in_range_machine_difference_is_its_integer_difference.md`,
`mdtests/an_operation_identity_bound_outside_its_type_is_refused.md`,
`mdtests/integer_operation_identity_of_a_product.md`,
`mdtests/a_product_identity_bound_outside_its_type_is_refused.md`).

The Integer certificate's `type_range => MIN <= to_integer(v);` (or
`to_integer(v) <= MAX`) states the range of a machine observation's type,
with the type's exact endpoint. It needs no premise.

`operation_bound => P;` states the bound a machine quotient, right shift,
or remainder by a positive constant takes from its operand. Unsigned
division truncates, which is the floor, so `q = x / c` with constant `c > 0`
has `c * q <= x` and `x <= c * q + (c - 1)`; `x >> k`, for a constant `k`
below the width, is `x / 2^k`; and `x % c <= c - 1`. Signed division
truncates toward zero, so its remainder has the sign of `x`: `c * q - (c -
1) <= x <= c * q + (c - 1)`, and `-(c - 1) <= x % c <= c - 1`. A signed
arithmetic shift is still the floor, with the unsigned form. The kernel
finds the operation among `P`'s machine observations and recomputes the
bound (`kernel::machine_integer::bounds::operation_bound`). A divisor that
is not a positive constant of the operation's format (a signed `0xfffffff8`
is `-8`), a symbolic divisor, a shift by the width or more, and a narrow or
128-bit operation give none
(`mdtests/solve_bounds_a_signed_quotient_by_its_operand.md`).
`excluded_bound N: D => P;` cites premise `N`, a disequality of a
machine value with its type's minimum or maximum, as the bound it gives: an
unsigned `v != 0` is `1 <= to_integer(v)` (`excluded_type_bound`).
`less_than_from_not_equal i, N: D => P;` makes node `i`'s non-strict bound
`t <= 0` strict, `t + 1 <= 0`, by premise `N`, a disequality whose
difference is `t` or `-t` (`integer_disequality_claims`): over the integers
`t <= 0` and `t != 0` leave `t <= -1`. It reads the one bound node and the
one premise, as written or as a native comparison's Integer reading, so it
holds at every format and over `Integer`. The refutation planner adds the
strict rows only when the linear facts leave a counterexample, from an index
of the premise and negated-goal bounds keyed by their difference, one
lookup per disequality
(`mdtests/a_bound_and_a_disequality_give_a_strict_64_bit_bound.md`).

An Integer certificate premise that compares exact observations of one
machine type, such as `1 <= to_integer(x)`, is also available when its native
comparison (`1u32 <= x`) is: the two hold together, which is the converse of
filing the native comparison beside an Integer fact.

`solve`'s selected-premise arithmetic uses all three. When the Integer facts
leave its refutation a
counterexample, it retries with the facts' native comparisons read as
Integer ones and with the type range of each machine observation, the
operation bound of each quotient, shift, or remainder by a constant,
and the bound each disequality with a type endpoint gives
(`mdtests/solve_bounds_an_unsigned_quotient_by_its_operand.md`,
`mdtests/solve_refuses_a_quotient_bound_past_the_floor.md`). When that
also fails, it may assume the identity of each machine `+`, `-` or `*` it
sees, reading a product of two observations as one opaque atom;
for each identity the refutation uses, it proves the two bounds with the
same arithmetic, applies `integer_operation_identity`, and then proves the
goal. When the arithmetic misses a bound of a product `to_integer(a) *
to_integer(b)`, the bound may still follow from the operands' type ranges:
`solve` compares the four corner products with it and, when they give it,
states each operand's two range bounds and proves the bound by
`integer_product_bounds` over them, which is what `click expand` writes. So
a `uint64` product's `0 <= to_integer(w) * to_integer(h)` needs no
requirement, and `to_integer(w * h) == to_integer(w) * to_integer(h)`
follows from the upper bound alone
(`mdtests/a_product_of_64_bit_values_is_its_exact_product.md`,
`mdtests/a_wrapping_64_bit_product_is_not_its_exact_product.md`). A product
whose bounds still miss is left unplanned and the other identities are kept.
So
`ensures result == x - 1;` for an unsigned
`x - 1u` verifies from `requires 1 <= x;` alone
(`mdtests/solve_proves_an_in_range_machine_sum_is_its_integer_sum.md`). The
retries run only after a miss, so a proof that needs none keeps its
certificate. An operand that is itself an operation gets its own identity,
proved first, so the bounds of `(a + b) + c` read `to_integer(a + b) ==
to_integer(a) + to_integer(b)` and `result == a + b + c` needs no stated step
(`mdtests/solve_observes_a_nested_sum_under_integer_arithmetic.md`). An
equality goal is proved from its two bounds, each inside its own `have`; when
the facts alone miss the first bound, the goal's own identities are proved
once beforehand, so both bounds read them, and a goal that is one of them
closes by `known`.

A typed integral cast is assumed the same way: `to_integer((T)x) ==
to_integer(x)`, proved by `integer_cast_identity` from `x`'s bounds inside
`T`'s range. With `1u64 <= x` and `x < 1000u64`, `1u32 <= x as uint32` follows,
and an `int` narrowed from a `long` reads its value the same way. A 64-to-32-bit
word narrowing does not record its operand's signedness, so the identity names
the operand the facts observe. An identity whose spelling names a different
observation, such as the signed reading of an unsigned narrowing's word, which
spells as the unsigned cast, is dropped and the refutation planned again
(`mdtests/solve_reads_a_narrowing_cast_inside_its_range.md`,
`mdtests/solve_does_not_read_a_narrowing_cast_outside_its_range.md`).
`solve() using` plans `integer_cast_identity` for an identity goal from two
listed constant bounds on the operand.

These are the shapes `solve`'s selected-premise arithmetic reads: linear claims over observations, the
facts' native comparisons, type ranges, operation and excluded bounds, and the identities of the in-range
`+` and `-` the goal and facts observe, nested or not. A miss on a claim of
that shape is a defect. A step that needs a choice is not in it: a cast that
keeps its value only under a range condition (`int32` to `uint32`), a
nonlinear fact, or a lemma to apply is written explicitly, as with
`integer_cast_identity`.

After its other searches, `solve` also closes a native comparison of exact
observations, such as a machine `result <= 50`, by proving its Integer
reading `to_integer(result) <= 50` this way; the Integer fact then supplies
the native one. To cite a fact, `solve` needs a source spelling for it. A
callee's Integer postcondition at the call site is spelled from the current
state, an observation of a value the proof has since replaced is spelled at
function entry (`old(*p)` for a written `*p`), and a native fact read as an
Integer one is spelled from the native fact's own operands
(`mdtests/solve_reads_a_call_postcondition_for_a_machine_bound.md`,
`mdtests/solve_spells_a_replaced_value_at_function_entry.md`).

## Bounded polynomial identities and quotient shifts

The explicit `rules` node
`integer_polynomial_identity bounds [] => L == R;` checks an equality in the
Integer ring. It expands addition, subtraction, negation, and multiplication;
all other roots, including truncating quotients, pure applications, folds, and
machine observations, are opaque atoms identified by shared Integer DAG nodes.
It never distributes native machine operations or cancels a denominator.
Its bounds list must be empty: it reads no premise or ambient environment.

The checker uses an iterative DAG traversal with local memoized polynomial
maps. Each node is expanded once, with hard limits of 256 ring DAG nodes,
256 monomials per intermediate polynomial, degree 16, and 4096-bit
coefficients. These limits bound each local map operation; exceeding a limit
returns a prompt structural-limit refusal. Magnitude-dependent arithmetic, map
operations, and monomial construction are charged before the work. There is
no unbounded polynomial expansion or nonlinear search. Kernel regressions
check fixed-width DAG growth, certificate-node growth, unrelated premise
populations, expansion caps, and exact deterministic budget boundaries.

The companion node `integer_quotient_shift bounds [i, j] => P;` checks exactly

```text
truncating_quotient(x + d * k, d) == truncating_quotient(x, d) + k
```

where `d` is a positive constant, premise `i` is `0 <= x`, and premise `j`
is `0 <= k`. Operand identities, guard polarity, and references must match
exactly. This follows from floor division on nonnegative numerators; it needs
no divisibility or parity premise. Both guards matter because truncation can
cross zero. Forms normalized away at lowering, such as division by one, are
proved with `normalize` instead. The checker performs only the two explicit
premise lookups and root-local shape checks; its work is independent of the
unused premise population.

`rewrite` accepts exact available mathematical Integer equalities as well as
machine equalities. Integer substitution follows the arithmetic spine through
products and quotients and pure-function arguments, refuses entry into internal binders,
and uses the existing equality-admission and binder-capture checks. It does
not infer an equality or rewrite ambient facts. Together these rules prove
adler2's triangular successor and weighted lane-bound recurrence without
changing its Rust source. See the
[checked fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_polynomial_and_quotient_shift.md).
## Checked equality rewriting

`rewrite(a, b)` accepts mathematical Integer equality alongside native,
pointer and algebraic equalities. Its equality must be an exact available fact,
in either orientation. The kernel refines the selected goal by substituting
exact occurrences of `a` with `b`; the remaining goal still needs a proof.
Products and sums therefore need no nonlinear arithmetic search just to replace
one proved-equal operand. Truncating quotient/remainder terms, negations,
differences, pure-function arguments and explicit machine conversion payloads
use the same sort-preserving walker.

The walker memoizes shared Integer nodes, preserves machine widths and load
states, and never recursively rewrites its replacement. Work follows the
selected logical DAG rather than its expanded paths or ambient facts. Successful
rewrites do not build diagnostic naming tables or scan unrelated locals; refusal
constructs names for the selected proof state. Logical quantifiers are traversed only when neither side of the equality mentions their
binder. Entering an internal fold or match binder is currently refused; replacing
an exact whole fold does not enter that binder and remains supported.

<!-- verified-example: mdtests/integer_equality_rewrite.md -->
```click
theorem integer_product_congruence(a: Integer, b: Integer, d: Integer) {
    requires a == b;
    ensures a * d + a == b * d + b by {
        rewrite(a, b);
        solve();
    }
}
```

The unchanged Bitcoin fee-division proof uses this rule twice to establish
`to_integer(n) == to_integer(quot) * to_integer(d) + to_integer(mod)` after
checking both narrowing casts. This reconstruction equation is a foundation
for the remaining exact rounding contract.

Exact Integer congruence also preserves unrelated native expression syntax.
It does not fold a native cast or a known conditional just because the walker
visits it: native observations are opaque affine atoms whose identities must
still match the available checked facts. Integer payloads that contain the
cited term continue to rewrite.

For a native correction, first rewrite its checked mathematical addition
identity, then replace the observed quotient. A native division expression can
itself contain the mathematical quotient; reversing that equality before
removing the native addition may also substitute inside the native expression.

<!-- verified-example: mdtests/integer_observed_quotient_correction.md -->
```click
theorem observed_quotient_correction(q: int64, quotient: Integer) {
    requires defined(q + 1i64);
    requires to_integer(q) == quotient;
    ensures to_integer(q + 1i64) == quotient + 1 by {
        have to_integer(q + 1i64) == to_integer(q) + to_integer(1i64);
        rewrite(to_integer(q + 1i64), to_integer(q) + 1);
        rewrite(to_integer(q), quotient);
        solve();
    }
}
```

A strict native comparison transfers to its exact observations without
asking native affine arithmetic to expand a narrowed wide operand: the
comparison of observations is the native comparison itself.

The unchanged Bitcoin and synthetic fee-division sidecars relate native
remainder cases to the mathematical truncating remainder this way.
Within the joint numerator/divisor bounds described below, they
prove all four exact result formulas. Floor mode returns the truncating quotient
minus one precisely for a negative remainder; ceiling mode returns it plus one
precisely for a positive remainder. A zero remainder leaves the quotient
unchanged in both modes. The synthetic modular caller exports the same
formulas while framing its untouched memory. These guarantees retain the
nonzero divisor and narrowing/overflow evidence. The product-inequality
characterizations and wider mode-specific result-fit profiles follow below.


## Rounded quotient product intervals

`integer::multiply_add(a, b, c)` is the exact Integer distributivity law
`(a + b) * c == a * c + b * c`. It is a proof-backed library lemma using the
shared bounded `integer_polynomial_identity` certificate, with no new axiom.
It establishes no native multiplication safety and does not expand products
during ordinary affine normalization.

`integer::floor_from_remainder(n, d, q, r, value)` and
`integer::ceiling_from_remainder(n, d, q, r, value)` are proof-backed library
lemmas. Each requires a positive divisor, reconstruction `n == q * d + r`,
and `1 - d <= r <= d - 1`. Floor additionally requires `value == q - 1` when
`r < 0` and `value == q` otherwise; ceiling requires `value == q + 1` when
`r > 0` and `value == q` otherwise. They prove the defining intervals
`value * d <= n < (value + 1) * d` and
`(value - 1) * d < n <= value * d`, respectively. The zero remainder satisfies
both unchanged-quotient cases.

The unchanged Bitcoin `FeeFrac::Div` and synthetic modular caller apply these
shared lemmas to fixed-state native observations and the explicit truncating
quotient/remainder. Their four mode-guarded product inequalities use mathematical
Integer arithmetic, including successor/predecessor operations, and retain all
previous native evaluation, narrowing and correction guards. The joint scaled
numerator/divisor profile and the wider mode-specific result-fit profiles are
described below; the portable `DivFallback` implementation remains open.

Opaque atom collection stops at the product, quotient or remainder root, using
shared node identity without traversing its operands. Distinct source terms
remain distinct atoms; only an explicit checked equality can connect them.
Kernel oracle and mutation tests, missing-domain and native-definedness fixtures,
expansion/reverification and multi-size deterministic scaling regressions pin
that boundary.


## Scaled positive-divisor quotient bounds

`integer_quotient_bound bounds [i, j] => b <= truncating_quotient(n, d);`
checks exactly two named Integer premises: `b * d <= n`, followed by
`1 <= d`. The upper form checks `n <= b * d` and concludes
`truncating_quotient(n, d) <= b`. The bound `b` may be negative or symbolic.
For a positive divisor, truncating division is monotone in its dividend and
an exact integer multiple divides to its factor. No rectangular interval or
ambient fact search is needed. Product operands must match the constructor's
normalized order; the checker does not search for polynomial equivalents.

The proof-backed `integer::positive_divisor_quotient_lower` and
`integer::positive_divisor_quotient_upper` library lemmas expose the rule.
Division's nonzero guard and all native evaluation/narrowing guards remain
separate obligations. The node reads two premise indices and shared operand
identities; its work does not grow with unrelated premises or shared DAG depth.
Opaque operands are never cloned; constant-product folding is charged before
computation.
See the [checked fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_quotient_bound.md).

The proof-backed `integer::positive_divisor_quotient_strict_lower` and
`integer::positive_divisor_quotient_strict_upper` expose strict scaled bounds.
They additionally require a negative lower bound or a positive upper bound:
truncation toward zero makes the unrestricted strict statements false (for
example, `-1 / 2` truncates to zero). Their proofs use the existing quotient
rule, signed remainder facts and reconstruction; no new kernel rule or search
is involved. The [strict-bound fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_quotient_strict_bound.md)
proves the int64 quotient fit needed by floor's `MIN * d <= n < (MAX + 1) * d`
and ceiling's `(MIN - 1) * d < n <= MAX * d` domains. These mathematical
quotient-fit results alone do not establish native narrowing or correction
safety. The separate Bitcoin `FeeFracDivResultFitDown/Up.click` sidecars now
prove those obligations on the unchanged source, using the strict lemma only
on the selected mode's widened boundary.

The unchanged C++ rounding sidecars now use joint guards
`-K * to_integer(d) <= to_integer(n) <= K * to_integer(d)` (two clauses).
The initial margin profile used `K = INT64_MAX - 1`; the endpoint proof below
widens it to `INT64_MIN * d <= n <= INT64_MAX * d`. Both profiles include
int128 numerators outside int64 and every positive int32 divisor. The broader
mode-specific result-fit contracts are verified as alternative helper profiles;
the alternative wide fee callers now compose them under explicit product-fit
premises without `at_size <= size`. Alternative unsigned fast callers also use
explicit upper product-fit bounds: Down bounds the product quotient, while Up
first bounds the adjusted numerator `product + size - 1`. Rectangular product
bounds check the actual uint64 operations independently of size, and the strict
quotient bound checks the int64 return cast. The alternative unified callers
now combine these fast and wide proofs under one full-signed-fee contract per
mode, using the same product-fit bounds and native amount bounds. Checked
source-comparison bridges derive the fast fee observer range within its
branch; both caller levels retain exact rounding and field frames. The original
joint amount/size profile remains a separate regression.


## Remainder signs and correction endpoints

`integer::lower_correction_bound(n, d, q, r, lower)` requires `lower <= q`,
`lower * d <= n`, reconstruction `n == q * d + r`, and `r < 0`. It proves
`lower + 1 <= q`: equality at the lower endpoint would contradict the scaled
input bound. The companion `integer::upper_correction_bound` uses `q <= upper`,
`n <= upper * d` and `0 < r` to prove `q <= upper - 1`. These are proof-backed
Integer lemmas; no divisor positivity or new arithmetic kernel rule is needed
once the stated reconstruction and bounds are supplied. Products remain opaque
until a checked equality substitutes the endpoint. Native correction safety
remains a separate obligation.

The unchanged Bitcoin and synthetic C++ sidecars apply these lemmas inside the
remainder-sign branches. This admits the inclusive joint profile
`INT64_MIN * d <= n <= INT64_MAX * d`, retains both exact correction formulas
and floor/ceiling product intervals, and includes exact division at both native
endpoints. The modular caller frames unrelated memory. Neither `quot + 1` nor
`quot - 1` is asserted to be defined unconditionally at those endpoints.
See the [checked fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_correction_endpoint_bounds.md).

Integer equality certificates produced from normalized opposite bounds now
retain the checked goal's spelling at their conclusion. For example, `b <= x`
and `not (b + 1 <= x)` prove `x == b` even though the source operands are not
syntactic opposites. The kernel still recomputes every premise and node; this
adds no search or unchecked equality. Expansion preserves the certificate and
reverifies, including rejection of forged equality results.


The shared parser admits `-9223372036854775808i64` as a native int64
constant, including when a proof is printed and parsed again. Its extra
magnitude is accepted only directly after unary minus: the positive suffixed
literal remains out of range. Negating the minimum is a separate native
operation and still requires definedness. See the
[minimum-literal fixture](https://github.com/clicklang/click/blob/master/mdtests/signed_int64_minimum_literal.md).


### Explicit multiplication ordering

`integer_multiply_order bounds [i, j] => a * factor <= b * factor;`
reads exactly `a <= b` and `0 <= factor`. With `factor <= 0` as the
second premise it instead checks `b * factor <= a * factor`. Each product
may put its factor on either side. Root-local constant, zero and one folding
is matched without traversing opaque operands; constant multiplication work
is charged before computing it. Negated/strict premises, mismatched operands,
missing signs and reversed conclusions are rejected. The checker reads two
selected premises and performs no ambient search or native range inference.

The proof-backed `integer::multiply_order_nonnegative` and
`integer::multiply_order_nonpositive` lemmas expose those cases.
`integer::scaled_product_bounds` composes them: if `lower <= value <= upper`,
`lower <= 0 <= upper`, and `0 <= amount <= size`, then
`lower * size <= value * amount <= upper * size`.
This establishes the fee caller's joint numerator/divisor profile for a full
int64 fee, but native multiplication observations, conversions, safety and
the caller's fast paths remain separate obligations. See the
[checked fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_multiply_order.md).


When `peel` removes the final Integer fold application from a goal, ordinary
source lowering may reduce its spelling to `true` while the kernel retains
an Integer comparison such as `0 - 0 == 0` or `0 <= 0`.
A trivial certificate preserves the constant comparison’s relation when it
matches that kernel goal, including at the conclusion. The refreshed spelling
is retained
when its lowered Integer claim matches the kernel checker's normalized claim,
or after a premise-free Integer certificate checks a truth reduced to a
Boolean constant. Later arithmetic certificates still discharge the original
kernel obligation; refreshing its presentation supplies no premise or memory
authority.
