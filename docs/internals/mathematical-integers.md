# Mathematical integers

`Integer` is Click's exact, signed mathematical number type for
specifications. It is separate from every C integer type and has no C storage,
ABI, machine width, or implicit runtime allocation. The kernel and standard
library may represent it internally in implementation-specific ways, but the
surface contract below is stable.

## Type and conversions

The public name is `Integer`; there is no `Int` alias. Existing `int` remains
the C `int32` type. Integer literals are arbitrary-size mathematical values
when their context is `Integer`. Machine values and Integer values do not mix
implicitly.

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

The checked `uint32_less_equal_to_integer` and
`uint32_to_integer_less_equal_implies_less_equal` laws preserve and reflect unsigned non-strict
order. Each requires the corresponding order premise. Unlike signed casts,
these observations retain values above `2147483647` through `4294967295`.
The proved library theorem `uint32_to_integer_bounds(value)` supplies
`0 <= to_integer(value) <= 4294967295` from the native unsigned range.
These laws preserve the value of a wrapping expression as evaluated; they do
not make its observation equal an unbounded mathematical sum. Observation of
an undefined expression still requires its definedness prerequisites.

The proved `uint32_less_than_to_integer` theorem transfers strict unsigned
order through the same exact observation. The checked
`uint32_remainder_less_than_divisor` rule requires a nonzero native divisor and
bounds `value % divisor` strictly below it for every u32 dividend. Combining
these with `uint32_to_integer_bounds` bounds the remainder's Integer observation
without changing its unsigned meaning or defining division by zero.

`uint32_less_than_divisor_implies_remainder_is_value(value, divisor)` proves `value % divisor == value`
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

Capturing an Integer expression as one symbolic term follows the same rule.
A partial machine operation inside the expression -- the `hi - 1` of a fold
range `(lo..(hi - 1))`, for instance -- makes the captured value the value of
only one evaluation path, guarded by that operation's definedness condition.
The capture is accepted when the proof context already states that condition
by an exact route, because then the guarded path is the only live one and
admitting the condition adds nothing to what the captured term asserts. It is
refused when the condition is not available, and the refusal names the
offending subterm -- the fold's range endpoint, initializer, or body -- along
with the condition that is missing. A missing condition is never dropped.

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
[deep quantifier scaling issue](https://github.com/clicklang/click/blob/master/issues/deep-quantifier-scaling.md).

For an existential witness, definedness remains attached to that same witness.
It cannot be weakened into an implication whose guard is false, since that
would permit an irrelevant witness to establish the existential claim.

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

Memory loads and fold atoms retain exact snapshot identity. Alpha-equivalent
loads from one retained snapshot may match; a different snapshot, body,
carrier, or definedness context does not. Snapshot identity is opaque to
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
fold over the snapshot before the write.

## Shared machine constants

`MachineIntegerFormat` records signedness and one of the fixed widths 8, 16,
32, 64, or 128. `MachineIntegerConstant` pairs that format with a checked
two's-complement payload; its private fields prevent oversized payloads from
entering a consumer. The inclusive bounds, literal checking, numeric observation,
and conversion policies share this representation. Boolean values remain a
separate source type. Width gives the number of value bytes, not ABI alignment
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

The shared kernel `c_integer_cast_modulo` boundary implements Rust integer `as`
and C++20 integral conversions for the admitted 8–64-bit runtime types. It
checks the evaluated source and destination types, folds root constants through
`MachineIntegerConstant`, and retains symbolic operands in the common term
arena. Narrow signed results keep the existing sign-extended 32-bit carrier;
unsigned results retain the low destination bits. Widening uses source
signedness before the destination interpretation. Conversion construction
inspects only a bounded number of root nodes.

Boolean sources observe their normalized zero-or-one numeric value. Boolean
results, floats, pointers, arrays, and unsupported widths are refused at this
integer boundary; their ordinary conversions use their own rules. Evaluation
of the operand still carries its definedness obligations, including overflow.
This explicit policy does not relax ordinary C casts or checked Integer
conversions. Casts involving 128-bit values use `MachineIntegerCast`, retaining
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

## Wide runtime scalars

The shared kernel has `CType::Int128` / `UInt128` and corresponding `CValue`
wrappers in the existing machine-term arena. `c_int128_literal` and
`c_uint128_literal` retain all 128 bits in `MachineIntegerConstant` payloads.
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
alpha keys, snapshot identities, and bounded walks keep the full payload.

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
snapshot/address/kind identity and certified defining facts. Their kinds retain
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
startup preserves full-width initializers; ordinary function entry supplies
symbolic storage without restoring those initializers or granting resources.
Symbolic arrays use the shared lazy storage runs, so entry and a selected read
do not visit unrelated elements. Compact scalar-copy checks include a wide
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
and snapshot matching must scale with the selected expression and certificate,
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
    ensures truncating_quotient(a, b) == truncating_quotient(a, b) by simp;
    ensures truncating_remainder(a, b) == truncating_remainder(a, b) by simp;
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


The shared library now exposes `integer_truncation_identity` under `d != 0`,
relating the symbolic terms by `n == truncating_quotient(n, d) * d +
truncating_remainder(n, d)`. For positive `d`, retaining the nonzero domain
premise,
`integer_positive_divisor_remainder_lower` and
`integer_positive_divisor_remainder_upper` establish `1 - d <= r <= d - 1`.
`integer_nonnegative_dividend_remainder` and
`integer_nonpositive_dividend_remainder` establish the corresponding remainder
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
        apply(integer_truncation_identity(n, d));
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
    ensures z == z by simp;
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

`int64_add_to_integer` and `int64_subtract_to_integer` extend the signed int32
observation laws to the full signed 64-bit carrier. Their kernel implementation
is shared with the int32 laws. Each exact observation requires the corresponding
native `defined(left + right)` or `defined(left - right)` fact. Modular machine
terms alone do not establish mathematical addition/subtraction, and an overflow
case cannot discharge the guard. Declaration checks retain the signed width,
operation, guard polarity and exact conclusion.

The unchanged Bitcoin division sidecar uses the addition law for the three
possible correction values after proving each native sum is defined. Explicit
Integer arithmetic then bounds those corrected observations before the original
short-circuit expression executes. Signed order reflection restores native bounds
on the actual returned value. This proves output bounds for both rounding
branches; identifying the result as a mathematical floor/ceiling remains separate.
Boundary oracles, forged declarations, missing/false guards, expansion,
reverification and deterministic application scaling cover the shared laws.
See the checked
[operation fixture](https://github.com/clicklang/click/blob/master/mdtests/int64_integer_operation_bridges.md).


## Exact unsigned 64-bit observations

The shared `uint64` observation bridges preserve unsigned semantics, including
values above `INT64_MAX`. Their premise is explicit; `defined(a + b)` alone
cannot exclude unsigned wrapping.

| Standard theorem | Required premise | Exact observation |
| --- | --- | --- |
| `uint64_add_to_integer` | `A + B <= UINT64_MAX` | `to_integer(a + b) == A + B` |
| `uint64_multiply_to_integer` | `A * B <= UINT64_MAX` | `to_integer(a * b) == A * B` |
| `uint64_subtract_to_integer` | `B <= A` | `to_integer(a - b) == A - B` |
| `uint64_divide_to_integer` | `b != 0u64 and B != 0` | `to_integer(a / b) == truncating_quotient(A, B)` |
| `uint64_remainder_to_integer` | `b != 0u64 and B != 0` | `to_integer(a % b) == truncating_remainder(A, B)` |
| `uint64_less_equal_to_integer` | `a <= b` | `A <= B` |
| `uint64_to_integer_less_equal_implies_less_equal` | `A <= B` | `a <= b` |

Here `A = to_integer(a)`, `B = to_integer(b)` and
`UINT64_MAX = 18446744073709551615`. Each is a kernel standard theorem with
checked parameter types, declaration shape, exact premise and conclusion.
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
The standard-library `int32_to_integer_less_equal_implies_less_equal` and
`int64_to_integer_less_equal_implies_less_equal` lemmas restore native order from an exact
Integer comparison. `int64_less_equal_to_integer` supplies the forward direction,
matching the existing int32 bridge. `int64_to_integer_equal_implies_equal` extends the
existing int32 injectivity bridge to the full signed 64-bit carrier.
`uint32_to_integer_equal_implies_equal` is the same injectivity bridge for the unsigned
32-bit carrier: equal pattern bits do not depend on signedness, and every
pattern has one unsigned Integer value.

These are width-specific kernel standard theorems with checked declaration
shape, parameter types, premise and conclusion. They require no overflow fact
because an already-existing signed bit pattern has one exact Integer value.
They infer neither implicit ranges nor narrowing identities. Prove the cast
identity and transport its Integer bounds before applying the reverse order
bridge to the narrowed native result. The C++ regression uses a range strictly
smaller than either native carrier, retains expansion/reverification and audit,
and frames unrelated memory through a modular caller.

Boundary models include both signs and full-width extrema; forged declarations,
missing/reversed premises, wrong carriers, false native bounds, and incorrect
certificate references are refused. See the checked
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
`int32_less_equal_to_integer` bridge. Excluding `0` and `-1` from
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

Nested conversions are compared with the canonical modulo cast of the source
observation, including a narrowing cast that discards an intermediate cast.
Unsigned byte readback also admits an exact low-bit mask: a `uint32` source
masked by `255` for a `uint8` observation or `65535` for a `uint16` observation.
Both forms require the same two range bounds. A specification's narrowing
into `int8`, `uint8`, `int16` or `uint16` keeps the source's 32-bit carrier,
or the low word of a 64-bit source, without a cast node; the rule admits
exactly those two carriers, again with bounds on the source observation
inside the destination range. C's narrowing into those types is a typed
`MachineIntegerCast` node; the rule compares it with the canonical cast, and
also looks through a C conversion from a 32-bit type that contains the
destination (`(uint16)(int32)w`) to the carrier beneath it, under the same
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

`rewrite(a == b)` accepts mathematical Integer equality alongside native,
pointer and algebraic equalities. Its equality must be an exact available fact,
in either orientation. The kernel refines the selected goal by substituting
exact occurrences of `a` with `b`; the remaining goal still needs a proof.
Products and sums therefore need no nonlinear arithmetic search just to replace
one proved-equal operand. Truncating quotient/remainder terms, negations,
differences, pure-function arguments and explicit machine conversion payloads
use the same sort-preserving walker.

The walker memoizes shared Integer nodes, preserves machine widths and load
snapshots, and never recursively rewrites its replacement. Work follows the
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
        rewrite(a == b);
        simp();
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
        apply(int64_add_to_integer(q, 1i64));
        rewrite(to_integer(q + 1i64) == to_integer(q) + 1);
        rewrite(to_integer(q) == quotient);
        simp();
    }
}
```

The proof-backed `int32_less_than_to_integer` lemma transfers a strict native
comparison without asking native affine arithmetic to expand a narrowed wide
operand. It follows from `int32_to_integer_less_equal_implies_less_equal`: if the mathematical
order were reversed or equal, reflecting that non-strict order would contradict
the strict native premise. No new kernel axiom or machine range assumption is
needed.

The unchanged Bitcoin and synthetic fee-division sidecars now use this lemma
to relate native remainder cases to the mathematical truncating remainder.
Within the joint numerator/divisor bounds described below, they
prove all four exact result formulas. Floor mode returns the truncating quotient
minus one precisely for a negative remainder; ceiling mode returns it plus one
precisely for a positive remainder. A zero remainder leaves the quotient
unchanged in both modes. The synthetic modular caller exports the same
formulas while framing its untouched memory. These guarantees retain the
nonzero divisor and narrowing/overflow evidence. The product-inequality
characterizations and wider mode-specific result-fit profiles follow below.


## Rounded quotient product intervals

`integer_multiply_add(a, b, c)` is the exact Integer distributivity law
`(a + b) * c == a * c + b * c`. It is a proof-backed library lemma using the
shared bounded `integer_polynomial_identity` certificate, with no new axiom.
It establishes no native multiplication safety and does not expand products
during ordinary affine normalization.

`integer_floor_from_remainder(n, d, q, r, value)` and
`integer_ceiling_from_remainder(n, d, q, r, value)` are proof-backed library
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

The proof-backed `integer_positive_divisor_quotient_lower` and
`integer_positive_divisor_quotient_upper` library lemmas expose the rule.
Division's nonzero guard and all native evaluation/narrowing guards remain
separate obligations. The node reads two premise indices and shared operand
identities; its work does not grow with unrelated premises or shared DAG depth.
Opaque operands are never cloned; constant-product folding is charged before
computation.
See the [checked fixture](https://github.com/clicklang/click/blob/master/mdtests/integer_quotient_bound.md).

The proof-backed `integer_positive_divisor_quotient_strict_lower` and
`integer_positive_divisor_quotient_strict_upper` expose strict scaled bounds.
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

`integer_lower_correction_bound(n, d, q, r, lower)` requires `lower <= q`,
`lower * d <= n`, reconstruction `n == q * d + r`, and `r < 0`. It proves
`lower + 1 <= q`: equality at the lower endpoint would contradict the scaled
input bound. The companion `integer_upper_correction_bound` uses `q <= upper`,
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

The proof-backed `integer_multiply_order_nonnegative` and
`integer_multiply_order_nonpositive` lemmas expose those cases.
`integer_scaled_product_bounds` composes them: if `lower <= value <= upper`,
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
