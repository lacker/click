# Grammar and operators

This page summarizes the grammar shared by the more detailed [language
reference](index.md). It describes Surface Click, the syntax accepted in
`.click` files. Kernel Click is an internal representation and has no textual
user syntax.

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
| `predicate`, `function`, `theorem` | Top-level logic declarations; `function` also starts a C contract. |
| `abstract`, `resource` | Abstract and composite resource declarations. |
| `counted` | Compatibility-only rejected spelling for the former `counted resource`; use `resource`. |
| `int32`, `uint8`, `int`, `int32_t`, `unsigned char`, `uint8_t`, `void`, `struct` | Type words. The standard spellings alias the modeled C0 types; `void` is available only where the detailed type rules allow it. |
| `let`, `where` | Value abbreviation and existential-binding forms. |
| `requires`, `ensures`, `decreases` | Contract, theorem, function-totality, and loop-termination clauses. |
| `owns`, `views`, `consumes`, `produces` | Resource transfer clauses. |
| `immutable`, `mutable` | Effect clauses and structural effect items. |
| `invariant`, `step`, `initialize`, `preserve` | Loop structural items and phase proofs. |
| `contains`, `fact`, `if` | Composite-resource members and optional resource guard. `if` also forms expressions and proof splits. |
| `read`, `write`, `object`, `memory`, `of`, `count` | Memory-resource forms, quantified resources, and resource-population expressions. |
| `and`, `or`, `implies`, `not` | Proposition connectives in increasing precedence, except right-associative `implies`. |
| `forall`, `exists` | Universal and existential quantifiers. |
| `all`, `any`, `fold` | Range proposition and expression methods. |
| `defined`, `loadable`, `separate` | Definedness, readable-memory, and resource-separation propositions. |
| `old`, `at`, `c` | Snapshot selection and embedded C-fragment forms. |
| `sizeof`, `byte_offset` | Supported scalar, pointer, and struct-layout sizes plus byte-granularity pointer-offset expressions. |
| `load_int32`, `load_uint8`, `load_int32_pointer`, `load_uint8_pointer`, `load_int32_pointer_pointer`, `load_uint8_pointer_pointer` | Typed memory-load expressions used by checked expansion when no higher-level source spelling is available. |
| `by`, `auto`, `using` | Proof introduction, default smart proof, and exact-premise syntax. |
| `mark`, `step`, `execute`, `execute_until`, `frame` | Execution and framing tactics. |
| `unfold`, `fold`, `observe`, `open` | Predicate and resource tactics. |
| `apply`, `have`, `if`, `cases`, `branch`, `loop` | Theorem application and structural proof tactics. |
| `witness`, `choose`, `from`, `requirement` | Existential evidence and fact selection. |
| `assumption`, `extract`, `normalize`, `intro`, `split`, `left`, `right`, `enumerate`, `contradiction` | Explicit proposition tactics. |
| `rewrite`, `transport`, `instantiate`, `simp`, `induct`, `close_invariants` | Equality, snapshot, quantifier, simplification, induction, and loop-proof tactics. |
| `as`, `else`, `ensuring`, `then` | Names and branches inside structural proof forms. |
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
                  | predicate-declaration
                  | function-declaration
                  | resource-declaration
                  | theorem-declaration
                  | c-function-contract
verifying-declaration := "verifying" string-literal ";"
predicate-declaration := "predicate" identifier parameters proposition-block
function-declaration  := "function" identifier parameters
                         ("->" type)? decreases-clause? expression-block
resource-declaration  := "resource" identifier parameters resource-body
theorem-declaration   := "theorem" identifier parameters theorem-body
c-function-contract   := "function" c-signature contract-body
```

Declaration order doesn't create a textual scope: validation builds the
declaration environment before it checks uses. Names must satisfy the
namespace rules in [Declarations](index.md#file-shape).

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
| 1 | `\|` | Left |
| 2 | `^` | Left |
| 3 | `&` | Left |
| 4 | `<<`, `>>` | Left |
| 5 | `+`, `-` | Left |
| 6 | `*`, `/`, `%` | Left |
| 7 | unary `-`, `~`, dereference `*` | Prefix |
| 8 | indexing `[]`, field access `->` | Left, postfix |
| 9 | literals, names, calls, ranges, conditionals, folds | Not applicable |

Comparisons form propositions rather than contract expressions. See
[Propositions](index.md#propositions) for their syntax and typing rules.

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

Omitting a proof and writing `by auto` request smart proof construction. Smart
search can advance proof state only through checked operations. Use
[`click expand`](../cli/expand.md) to replace expandable smart proof sites with
the corresponding explicit proof steps; Click verifies the complete rewritten
source.
