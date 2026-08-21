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

```click
(lo..hi).all(|k| { p[k] == 0 })
(lo..hi).any(|k| { p[k] == needle })
(lo..hi).fold(0, |acc, k| { acc + p[k] })
```

Quantifiers use an explicitly typed binder:

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

Omitting a proof and writing `by auto` request smart proof construction. A
successful smart proof is accepted only after its simple certificate replays.
Use [`click expand`](../cli/expand.md) to replace expandable smart proof sites
with the replayable simple steps.
