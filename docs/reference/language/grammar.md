# Grammar and operators

This page summarizes the grammar shared by the more detailed [language
reference](index.md). It describes Surface Click, the syntax accepted in
`.click` files. Kernel Click is an internal representation and has no textual
user syntax.

The recursive parser currently supports at most 16 nested parentheses and
16 nested `match` expressions. Excessive nesting is rejected with a source
diagnostic rather than risking a native stack overflow.

## Lexical conventions

Identifiers start with an ASCII letter or underscore and continue with ASCII
letters, decimal digits, or underscores. Keywords cannot be identifiers.
Whitespace separates tokens. Line comments start with `//`; block comments
start with `/*` and end with `*/`.

Integer literals are decimal. Character literals use single quotes, including
the ordinary C escapes accepted by the parser. String literals occur in source
locations and other explicitly documented string positions; Click doesn't
have a first-class string type.

## Word index

Surface Click uses contextual words rather than a separate token kind for
keywords. A spelling can be an ordinary identifier where the surrounding
grammar doesn't give it a special meaning. The implementation registry and
documentation inventory keep the following accepted words synchronized.

| Words | Context and status |
| --- | --- |
| `verifying` | C-source declaration. |
| `predicate`, `function`, `theorem`, `contract` | Top-level logic and behavioral-interface declarations; `function` also starts a C contract. |
| `executes` | Gives a contract-refinement theorem an explicit one-call execution frontier, over the theorem's callback parameter or a named project function. |
| `spec`, `enum`, `match` | Specification-only algebraic datatype declarations and exhaustive elimination. |
| `abstract`, `resource` | Abstract and composite resource declarations. |
| `counted` | Compatibility-only rejected spelling for the former `counted resource`; use `resource`. |
| `int16`, `int32`, `uint8`, `uint16`, `uint32`, `int64`, `uint64`, `short`, `int`, `long`, `long long`, `int16_t`, `int32_t`, `int64_t`, `ssize_t`, `unsigned char`, `unsigned short`, `unsigned int`, `unsigned long`, `unsigned long long`, `uint8_t`, `uint16_t`, `uint32_t`, `uint64_t`, `size_t`, `void`, `struct` | Type words. The standard spellings alias the modeled C0 types; `void` is available only where the detailed type rules allow it. |
| `let`, `where` | Value abbreviation and existential-binding forms. |
| `requires`, `ensures`, `decreases` | Contract, theorem, function-totality, and loop-termination clauses. A `decreases` clause is one expression, classified after name resolution as an int32 measure, a resource application, or a resource binder; there is no `decreases resource` spelling. |
| `owns`, `views`, `consumes`, `produces` | Resource transfer clauses, in a contract and in a loop header. |
| `constructs` | Authorizes one function to create an abstract resource token. |
| `invariant`, `initialize`, `preserve` | Loop structural items and phase proofs; a loop header also takes `owns` and `views` clauses of its own. |
| `contains`, `fact`, `field`, `if` | Composite-resource members, pure field declarations, and optional resource guard. `if` also forms expressions and proof splits. |
| `read`, `write`, `object`, `memory`, `of`, `count` | Memory-resource forms, quantified resources, and resource-population expressions. |
| `and`, `or`, `implies`, `not`, `in` | Proposition connectives and sequence membership. `and`, `or`, and `implies` have increasing precedence except right-associative `implies`; `in` has comparison precedence. |
| `forall`, `exists` | Universal and existential quantifiers. |
| `all`, `any`, `fold` | Range proposition and expression methods. |
| `defined`, `loadable`, `separate`, `aligned` | Definedness, readable-memory, resource-separation, and pointer-alignment propositions. |
| `old`, `at`, `c` | Snapshot selection and embedded C-fragment forms. |
| `sizeof`, `byte_offset`, `address` | Supported scalar, pointer, and struct-layout sizes, byte-granularity pointer-offset expressions, and the LP64 integer representation of an object pointer. |
| `load_int32`, `load_uint8`, `load_uint32`, `load_int64`, `load_uint64`, `load_int32_pointer`, `load_uint8_pointer`, `load_int32_pointer_pointer`, `load_uint8_pointer_pointer` | Typed memory-load expressions used by checked expansion when no higher-level source spelling is available. |
| `by`, `auto`, `using` | Proof introduction, default smart proof, and exact-premise syntax. |
| `mark`, `step`, `execute`, `execute_until` | Execution tactics. |
| `unfold`, `fold`, `observe`, `construct`, `open` | Predicate and resource tactics. |
| `apply`, `have`, `if`, `cases`, `both`, `branch`, `loop` | Theorem application and structural proof tactics. |
| `witness`, `choose`, `from`, `requirement` | Existential evidence and fact selection. |
| `assumption`, `extract`, `normalize`, `intro`, `split`, `left`, `right`, `enumerate`, `contradiction` | Explicit proposition tactics. |
| `arithmetic_certificate` | Starts the typed arithmetic-certificate envelope. The canonical mathematical family is `arithmetic_certificate { ... }`; checked machine families are `arithmetic_certificate signed_int32 { ... }` and `arithmetic_certificate special { ... }`. `integer_certificate { ... }` remains a parser-only legacy alias for the mathematical family. |
| `signed_int32` | Selects the public checked signed-machine arithmetic-certificate family. |
| `special` | Selects the pointer, tagged-word, and finite-float arithmetic-certificate family. |
| `premise` | Names an exact premise node in an arithmetic certificate. |
| `scale` | Scales an earlier arithmetic certificate node by an exact decimal coefficient. |
| `add` | Adds two earlier arithmetic certificate nodes. |
| `eq_to_le` | Converts an equality certificate node to a non-strict bound. |
| `eq_from_bounds` | Closes an equality from opposite non-strict bounds. |
| `trivial` | Checks a context-free affine identity. |
| `interval_from_affine`, `interval_atom`, `interval_intersect` | Introduce, or intersect, checked signed-machine intervals. |
| `defined`, `interval_add`, `interval_add_bounded`, `interval_subtract`, `interval_multiply`, `interval_remainder`, `interval_shift_left`, `interval_arithmetic_shift_right`, `interval_bitwise_and`, `interval_sign_bit_flip`, `interval_compare` | Record exact definedness premises and bounded interval-operation evidence for signed-machine expressions. |
| `affine_conclusion` | Bridges an affine claim to a machine proposition using the cited interval/definedness evidence. |
| `conclusion` | Selects the final node of an arithmetic certificate. |
| `reverse` | Selects the reverse equality direction for `eq_to_le`. |
| `rewrite`, `transport`, `instantiate`, `simp`, `induct`, `close_invariants` | Equality, snapshot, quantifier, simplification, induction, and loop-proof tactics. |
| `as`, `else`, `ensuring`, `then` | Names and branches inside structural proof forms. `as` also introduces the target contract's proof instances on an `executes` conclusion. |
| `function`, `loop`, `statement`, `entry`, `exit` | Program-region and program-point selectors. |
| `apply_loop_summary`, `bounded_execute`, `calculate`, `conjunction`, `double_negation`, `execute_else_step`, `execute_rest`, `execute_step`, `execute_then_step`, `summarize`, `symbolic_execute`, `vacuous` | Compatibility-only tactic spellings that produce focused migration diagnostics. |

See [Tactics](../tactics/index.md) for tactic syntax and classification. A word
listed here isn't necessarily valid in every identifier or expression
position; the construct entry defines its allowed context.

## File-level declarations

The following schematic grammar uses `...` for content defined on the linked
language-reference page:

```text
click-file       := item*
item             := verifying-declaration
                  | algebraic-declaration
                  | predicate-declaration
                  | function-declaration
                  | resource-declaration
                  | theorem-declaration
                  | named-contract-declaration
                  | c-function-contract
verifying-declaration := "verifying" string-literal ";"
algebraic-declaration := "spec" "enum" identifier type-parameters?
                         "{" variant ("," variant)* ","? "}"
type-parameters       := "<" identifier ("," identifier)* ">"
variant               := identifier ("(" field-type ("," field-type)* ")")?
predicate-declaration := "predicate" identifier parameters proposition-block
function-declaration  := "function" identifier parameters
                         ("->" type)? decreases-clause? expression-block
resource-declaration  := "resource" identifier parameters resource-body
theorem-declaration   := "theorem" identifier parameters executes-clause? theorem-body
executes-clause      := "executes" executed-function "(" c-parameters ")"
executed-function    := callback-parameter-name | c-function-name
executes-conclusion  := "ensures" proposition instance-map? proof
instance-map         := "as" "{" (identifier ":" identifier
                         ("," identifier ":" identifier)* ","?)? "}"
named-contract-declaration := "contract" c-signature contract-body
c-function-contract   := "function" c-signature contract-body
```

Declaration order doesn't create a textual scope: validation builds the
declaration environment before it checks uses. Names must satisfy the
namespace rules in [Declarations](index.md#file-shape).

The `executes` name is resolved by the conclusion, not by the clause: a
conclusion about a function address, `ensures Name(&f)`, executes the project
function `f`, and a conclusion about a binding, `ensures Name(cb)`, executes the
theorem's callback parameter `cb`. See
[Callback execution theorems](index.md#callback-execution-theorems).

## Proposition precedence

From lowest to highest precedence:

| Precedence | Form | Associativity |
| --- | --- | --- |
| 1 | `implies` | Right |
| 2 | `or` | Left |
| 3 | `and` | Left |
| 4 | prefix `not` | Prefix |
| 5 | atoms, predicate calls, comparisons | Not applicable |

Thus `p implies q implies r` means `p implies (q implies r)`, while `p or q
or r` means `(p or q) or r`. Use parentheses whenever grouping carries the
explanation.

## Contract-expression precedence

From lowest to highest precedence:

| Precedence | Operators or forms | Associativity |
| --- | --- | --- |
| 1 | sequence concatenation `++` | Left |
| 2 | `\|` | Left |
| 3 | `^` | Left |
| 4 | `&` | Left |
| 5 | `<<`, `>>` | Left |
| 6 | `+`, `-` | Left |
| 7 | `*`, `/`, `%` | Left |
| 8 | unary `-`, `~`, dereference `*` | Prefix |
| 9 | indexing `[]`, field access `->` | Left, postfix |
| 10 | literals, names, calls, constructors, matches, ranges, conditionals, folds | Not applicable |

Comparisons form propositions rather than contract expressions. See
[Propositions](index.md#propositions) for their syntax and typing rules.

## Algebraic datatypes

The algebraic-datatype slice supports generic, specification-only
sum-of-products declarations as first-class Click types. A
constructor is fully type-applied at its use site. Pure functions, predicates,
and theorems may receive arbitrary algebraic values, pure functions may return
them, and an exhaustive `match` may inspect an unknown variant and return a
common C or algebraic type:

Pure functions, predicates, and theorems may declare Rust-like type parameters
after their name. Calls and theorem applications infer each type argument from
the concrete argument types; there is no separate call-site type-argument
syntax. Each inferred function instance has a distinct typed kernel identity,
and an explicit `unfold` instantiates the signature and body before exposing
its defining equation:

<!-- verified-example: mdtests/algebraic_generic_functions.md -->
```click
function append<T>(xs: TestList<T>, ys: TestList<T>) -> TestList<T> {
    // ...
}

predicate is_empty<T>(xs: TestList<T>) {
    xs == TestList<T>::Nil
}
```

Inference rejects both unconstrained parameters and conflicting arguments.
Generic theorem declarations, including their proofs, are checked with rigid
arbitrary type parameters. An unused invalid proof is rejected. A parameter
supports typed symbolic values and equality, not arithmetic or constructor
elimination. At `apply`, Click infers the type arguments,
substitutes them through the theorem statement and proof, verifies that
monomorph, and caches the checked instance. An invalid generic proof therefore
grants no authority, and distinct applications such as `TestList<int32>` and
`TestList<int32*>` are checked as distinct instances:

<!-- verified-example: mdtests/algebraic_generic_theorems.md -->
```click
theorem append_right_identity<T>(xs: TestList<T>) {
    ensures append(xs, TestList<T>::Nil) == xs by {
        induct(xs) as ih {
            // ...
        }
    }
}
```

<!-- verified-example: mdtests/algebraic_maybe.md -->
```click
spec enum Maybe<T> {
    None,
    Some(T),
}

ensures match Maybe<int32>::Some(value) {
    Maybe::None => fallback,
    Maybe::Some(inner) => inner,
} == value;
```

Constructor equality is structural and checked against the resolved datatype
schema. Different variants are disjoint; an assumed equality between them is
a contradiction. Equality of every corresponding field proves equality of
two applications of one constructor (congruence), and an exact equality of
such applications exposes equality only at the same field position
(injectivity). `simp` can select these rules, expanding congruence to explicit
`rewrite` steps and injectivity to checked `extract` steps.

Pattern arms must name every variant exactly once, use the declared field
arity, and keep field bindings local to the arm. Generic arguments and fields
may be modeled C types or other fully applied algebraic types; nested generic
applications such as `Holder<Maybe<int32>>` are supported. Nested fields stay
as typed algebraic terms when bound by a symbolic match.

<!-- verified-example: mdtests/algebraic_nested_fields.md -->
```click
spec enum Envelope<T> {
    Missing,
    Present(Maybe<T>),
}
```

Datatype fields may recursively refer to their own declaration or to another
datatype in the same recursive group. Recursive occurrences are strictly
positive because field types contain values rather than functions, and the
currently supported regular form must preserve the enclosing type parameters
exactly. Every recursive group must have a finite constructor path. Schemas
remain finite nominal descriptions: `TestList<T>` in the `Cons` field refers back
to the same instantiated schema rather than expanding it.

<!-- verified-example: mdtests/algebraic_recursive_list.md -->
```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}
```

See the pure, C-free first-class regressions in
`mdtests/algebraic_symbolic_values.md` and
`mdtests/algebraic_nested_fields.md`, with recursive values covered by
`mdtests/algebraic_recursive_list.md`.

Expression-local `let` bindings use the same Click type family as parameters
and results. The annotation may name an algebraic type, or it may be omitted
when the value determines the type:

<!-- verified-example: mdtests/algebraic_symbolic_values.md -->
```click
let explicit: Maybe<int32> = Maybe<int32>::Some(value);
let inferred = wrap(value);
inferred
```

The bound name is a lexical specification binding. Lowering keeps an
algebraic value symbolic; it does not turn the binding into a C local or
execute the Click expression.

An algebraic parameter is one typed logical variable. Click does not encode an
unknown value by allocating a runtime-like tag or by eagerly constructing one
symbolic payload for every variant. Constructors and matches remain logical
terms; a match introduces constructor cases only when its definition is used
by a proof. This is specification elaboration, not execution of Click code or
of a logical value.

Algebraic quantifiers and resource arguments remain tracked in the algebraic
data types issue. A recursive pure function may name an algebraic parameter in
`decreases` and recurse on algebraic fields introduced by exhaustive matches
of that parameter or an already-smaller field. Such calls stay symbolic until
explicitly unfolded. A pure theorem may use constructor-branching
`induct(value) as ih { Type::Variant(fields) => { ... } ... }`; it requires one
arm per constructor and permits `ih(field)` for immediate fields of the same
recursive datatype. Mutual induction across distinct datatype families is not
yet generated. Reusing one constructor refinement across repeated matches is
tracked separately in the algebraic match path-correlation issue.

## Specification sequences

`[a, b, c]` is an immutable finite specification sequence. Its elements must
have one compatible C scalar or data-pointer type. `[]` is the empty sequence,
and `left ++ right` concatenates two compatible sequences without allocating C
memory or granting memory authority. Sequence values support `==`, `!=`, and
the proposition `element in sequence`; ordering comparisons are rejected.

Concatenation is associative and `[]` is its left and right identity. Sequence
equality compares elements rather than concatenation-tree shape, preserving
order and multiplicity.

`old(...)` and proof snapshots evaluate every element in the selected state,
so a contract can relate current array cells to their exact entry order:

<!-- verified-example: mdtests/sequence_literals.md -->
```click
ensures [destination[0], destination[1], destination[2]]
    == old([source[0], source[1], source[2]]);
```

This initial slice exposes literal sequence values in equality and membership
propositions. The standard library also supplies the algebraic `List<T>` with
`Nil`, `Cons`, append, and membership. Migration of the literal operators to
that library type, general indexing, and projection of a symbolic memory range
remain open.

## C0-expression precedence

C fragments use C-like precedence. From lowest to highest:

| Precedence | Operators | Associativity |
| --- | --- | --- |
| 1 | `||` | Left |
| 2 | `&&` | Left |
| 3 | `\|` | Left |
| 4 | `^` | Left |
| 5 | `&` | Left |
| 6 | `<`, `<=`, `>`, `>=`, `==`, `!=` | Left |
| 7 | `<<`, `>>` | Left |
| 8 | `+`, `-` | Left |
| 9 | `*`, `/`, `%` | Left |
| 10 | supported unary operators | Prefix |
| 11 | calls, indexing, member access | Left, postfix |

This table describes the parser, not all of ISO C. The normative set of types,
statements, and operators that Click accepts is in [Supported C0](c0.md).

## Ranges and binders

`lo..hi` denotes the half-open integer range whose elements satisfy `lo <= k <
hi`. A range can introduce a binder through `.all`, `.any`, or `.fold`:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
(lo..hi).all(|k| { p[k] == 0 })
(lo..hi).any(|k| { p[k] == needle })
(lo..hi).fold(0, |acc, k| { acc + p[k] })
```

Quantifiers use an explicitly typed binder:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
forall (x: int32) { x == x }
exists (x: int32) { x == value }
```

Binder scope is the body between braces. Renaming a bound variable doesn't
change the proposition or expression it denotes.

## Proof syntax

A proof is omitted, written `by auto`, or written as a `by { ... }` block of
tactic statements. Tactic arguments use the expression and proposition forms
documented for that tactic. The exhaustive surface-spelling inventory is in
[Tactics](../tactics/index.md).

One tactic carries syntax beyond an argument list: a `step` on an ordinary C
call writes the call as it appears in the source, maps the callee's instance
binders to the caller's instances, and introduces a produced instance with
`let`.

```text
call-step  := ("let" identifier "=")? "step" "(" c-call "," binder-map ")" ";"
binder-map := "{" (identifier ":" identifier
               ("," identifier ":" identifier)* ","?)? "}"
```

Omitting a proof and writing `by auto` request smart proof construction. Smart
search can advance proof state only through checked operations. Use
[`click expand`](../cli/expand.md) to replace expandable smart proof sites with
the corresponding explicit proof steps; Click verifies the complete rewritten
source.
