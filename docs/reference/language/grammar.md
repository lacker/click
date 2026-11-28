# Grammar and operators

This page summarizes the grammar shared by the more detailed [language
reference](index.md). It describes Surface Click, the syntax accepted in
`.click` files. Kernel Click is an internal representation and has no textual
user syntax.

The recursive parser bounds nested parentheses, `match` expressions,
conditional expressions, quantifier bodies, proof blocks, and sequence
brackets. Algebraic generic applications and fields have a separate type
nesting budget. Excessive nesting is rejected with a source diagnostic rather
than risking a native stack overflow.

## Lexical conventions

Identifiers start with an ASCII letter or underscore and continue with ASCII
letters, decimal digits, or underscores. Keywords cannot be identifiers.
Whitespace separates tokens. Line comments start with `//`; block comments
start with `/*` and end with `*/`. Block comments do not nest; an unclosed
block comment is a syntax error. `#` does not start a comment and is refused
with the `//` form. Comments preserve source locations and are ignored when
loading imports or selecting proof steps.

Integer literals are decimal in the default grammar, except within the
[exact float bit forms](#exact-float-bit-literals). Rust sidecars also accept
radix prefixes, underscore separators, and the suffixes described under
[Rust integer literals](../rust.md#integer-literals).
Character literals use single quotes, including
the ordinary C escapes accepted by the parser. String literals occur in source
locations and other explicitly documented string positions. The
[byte string syntax](#byte-string-literals) is available in specifications.

Call-style proof tactics require parentheses, including the no-argument
call `close()`. A single tactic call can follow `by` directly; braces enclose
a sequence and may also enclose one call. An omitted proof runs the whole
proof by automation.

## Byte string literals

`b"..."` denotes a `List<uint8>` in a Click expression. Printable ASCII
characters supply their byte values. The escapes `\0`, `\n`, `\r`, `\t`,
`\"`, `\'`, and `\\` supply individual bytes, and `\xNN` takes exactly
two hexadecimal digits. The list contains exactly those bytes, in order.
For example, `b"a\0b"` has three elements, and `b""` is
`List<uint8>::Nil`. A literal may contain up to 64 bytes after decoding.

The spelling has the same meaning in a C, C++, or Rust sidecar. The source
language supplies the encoding and terminator rules for its own literals.

<!-- verified-example: mdtests/byte_string_literals.md -->

## Exact float bit literals

`float32_from_bits(bits)` and `float64_from_bits(bits)` construct binary32 and
binary64 values from their exact IEEE bit patterns, without numeric conversion.
They preserve signed zero, infinities, and NaN signs and payloads. Each takes
exactly one nonnegative integer literal, within the unsigned range of that
width. The literal may be unsuffixed or have the matching `u32` or `u64` suffix.
Variables, arithmetic expressions, negative literals, and other suffixes are
refused. These are literal forms, not general bit-cast functions.

Both default Click and Rust sidecars accept radix prefixes and underscore
separators inside these forms. This does not enable Rust integer syntax
elsewhere in default Click. A matching suffix and an unsuffixed input
produce the same float literal. Exact source printing uses hexadecimal bits
with an unsuffixed literal for binary32 and a `u64` suffix for binary64.

Unary `-x` on a float flips its sign bit, including signed zero and NaN
payloads. It uses the same negation as C float expressions; integer unary
minus retains its existing arithmetic and definedness conditions
(`mdtests/float_unary_negation_preserves_signed_zero.md`).

<!-- verified-example: mdtests/float_bit_literals_preserve_ieee_values.md -->
```click
theorem float_bits() {
    ensures iszero(float32_from_bits(0x80000000u32)) by { close(); }
    ensures isnan(float64_from_bits(0x7ff8000000000123u64)) by { close(); }
}
```

## Typed loads

`load<T>(p)` reads the object at address `p` as type `T`. It is one memory
read with a type argument, the kernel's typed load, so it covers every type a
read can have:
- a scalar, such as `int8`, `uint64`, `int128`, `Bool`, `float`, or `double`
- a data pointer, such as `void*`, `int32*`, or `uint8**`
- a function pointer, written `R (*)(A, ...)`

`volatile T` makes the access volatile. `const T*` reads a pointer whose
pointee is `const`. A struct is not read whole: read its fields.

A C read such as `*p`, `p->f`, or `p[i]` already names its place. A
specification writes `load<T>` for a read whose address has no such place,
such as one byte of a wider cell, `load<uint8>(byte_offset(p, n))`.
Expansion writes it for the same reason. The type argument is explicit
because it is not the static type of `p`.

<!-- verified-example: mdtests/typed_load_built_in_on_comparison_left.md -->
```click
uint64 read64(uint64* p) {
    views p[0..1];
    ensures load<uint64>(p) == result;
} by { step(); close(); }
```

## Word index

Surface Click uses contextual words rather than a separate token kind for
keywords. Such a word can be an ordinary identifier where the surrounding
grammar doesn't give it a special meaning. The implementation registry and
documentation inventory keep the following accepted words synchronized.

| Words | Context and status |
| --- | --- |
| `import` | Loads declarations from a local Click module, or names a Click library module with `click::`, without selecting that module's proofs. |
| `verifying` | C-source declaration. |
| `target`, `mode` | Select the C implementation target the file's C sources are preprocessed and verified under: the target triple and its `kernel` or `userspace` mode. |
| `predicate`, `function`, `theorem`, `contract`, `tactic` | Top-level logic and behavioral-interface declarations; `tactic` declares a user-defined tactic. A C function's contract starts with its C return type, not `function`. |
| `executes` | Gives a contract-refinement theorem an explicit one-call execution frontier, over the theorem's callback parameter or a named project function. |
| `spec`, `enum`, `match` | Specification-only algebraic datatype declarations and exhaustive elimination. |
| `abstract`, `resource`, `authorized` | Abstract and composite resource declarations. `authorized resource` (or `authorized abstract resource`) marks a family that takes part in population accounting, so `authority(...)` and `count(...)` may name it. |
| `int8`, `int16`, `int32`, `uint8`, `uint16`, `uint32`, `int64`, `uint64`, `short`, `int`, `signed int`, `long`, `long long`, `int8_t`, `int16_t`, `int32_t`, `int64_t`, `ssize_t`, `signed char`, `unsigned char`, `unsigned short`, `unsigned int`, `unsigned long`, `unsigned long long`, `uint8_t`, `uint16_t`, `uint32_t`, `uint64_t`, `size_t`, `void`, `struct` | Type words. The standard names alias the modeled Click's C types; `void` is available only where the detailed type rules allow it. |
| `let`, `where` | Value abbreviation and existential-binding forms. |
| `requires`, `ensures`, `exceptional`, `throws`, `decreases` | Contract, theorem, function-totality, exceptional-postcondition, and loop-termination clauses. The initial exceptional signature is `throws int32`, with clauses written `exceptional ensures`; a `decreases` clause is one expression, classified after name resolution as a numeric (int32, unsigned, or `Integer`) measure, a resource application, or a resource binder; there is no `decreases resource` form. |
| `diverges` | Signature and `loop`-head marker declaring that the function or loop may not return. It follows the parameter list, after `throws` when a signature carries both, and excludes a `decreases` clause on the same function or loop. |
| `owns`, `views`, `consumes`, `produces` | Resource transfer clauses, in a contract and in a loop header. In a resource body, `owns` and `views` state what the resource holds, memory and child resources alike. `consumes X; produces X;` for one fixed `X` is refused: it is written `owns X;`. |
| `uninitialized` | `owns uninitialized(p[a..b])`, and the same in `consumes` and `produces`: memory held with no claim that its bytes are initialized. Only a function contract's owning clauses accept it; see [Uninitialized owned memory](index.md#uninitialized-owned-memory). |
| `constructs` | Authorizes one function to create an abstract resource token. |
| `invariant`, `initialize`, `maintain` | Loop structural items and phase proofs; a loop header also takes `owns` and `views` clauses of its own. |
| `contains`, `fact`, `field`, `if` | The containment proposition `contains(parent, child)`, resource facts, pure field declarations, and optional resource guard. A resource holds a child resource with `owns`, as it holds memory. `if` also forms expressions and proof splits. |
| `object`, `memory`, `of`, `count` | Memory-resource forms, quantified resources, and resource-population expressions. `count(r(args))` is the population operator when its one argument is a resource call; otherwise `count` names the prelude function. |
| `read`, `write` | Reserved: no resource may be named either. `read(N)` is also an execution target, below. |
| `true`, `false` | The specification `bool` literals, the C `bool` values `1` and `0`. A C name of either word in scope keeps its C meaning; a Click binder may not use them. See [Booleans](index.md#booleans). |
| `and`, `or`, `implies`, `not`, `in` | Proposition connectives and sequence membership. `and`, `or`, and `implies` have increasing precedence except right-associative `implies`; `in` has comparison precedence. |
| `forall`, `exists` | Universal and existential quantifiers; `exists (x: T, y: U) { P }` binds multiple variables. |
| `all`, `any`, `fold` | Range proposition and expression methods. |
| `prop` | Proposition value: `prop { P }`. |
| `defined` | The definedness [special form](index.md#special-forms), a proposition. |
| `viewable`, `same_allocation`, `separate`, `aligned`, `little_endian` | Readable-memory, pointer-provenance, resource-separation, pointer-alignment, and target-byte-order propositions. |
| `old`, `at` | Point-selecting [special forms](index.md#special-forms): `old(e)` reads at the function's entry, `at(point, e)` at a named point. |
| `program` | Program-binding qualifier: `program::name` names a program binding where a Click name has the same name. |
| `exact` | Point-selecting [special form](index.md#special-forms): `exact(place)` reads `place` named by the state in scope itself, with no version walk ([`exact(...)`](index.md#exact)). |
| `float32_from_bits`, `float64_from_bits` | Literal-only IEEE bit-pattern expressions; see [exact float bit literals](#exact-float-bit-literals). |
| `sizeof`, `byte_offset`, `address` | Supported scalar, pointer, and struct-layout sizes, byte-granularity pointer-offset expressions, and the LP64 integer representation of an object pointer. |
| `is_a` | Type-evidence proposition `is_a<T>(p)`: the object `p` points to is a `T`, a struct type `struct S` or a pointer to one `struct S*`. It holds where the proof has that evidence, such as an opened resource body's typed call. See [Type evidence](#type-evidence). |
| `load` | Typed memory read `load<T>(p)`: reads the object at `p` as `T`, a scalar, data pointer, or function pointer `R (*)(A, ...)`; `volatile T` makes the access volatile and `const T*` reads a pointer to `const T`. Expansion writes it for a read with no C place to name it. See [Typed loads](#typed-loads). |
| `by`, `using` | Proof introduction and exact-premise syntax. |
| `mark`, `step`, `step_until` | Execution tactics. `step` and `step_until` are [state tactics](../../concepts/smart-and-simple-tactics.md#state-tactics-and-logical-tactics) that change the program state; `mark` names the current point. |
| `unfold`, `fold`, `observe`, `with` | Predicate and resource tactics: state tactics that change the resource context. |
| `unfold` and `fold` with `[i]` or `[..]` | Expose or restore an iterated ownership slot, or form or dissolve the whole iterated fact. `forall` inside a resource body starts the iterated clause itself. |
| `apply`, `have`, `if`, `cases`, `all`, `branch`, `outcomes`, `loop` | Theorem application and structural proof tactics. |
| `both` | Retired conjunction tactic. Use `all { P => { ... } Q => { ... } }`. |
| `witness`, `obtain` | Existential introduction and elimination. `let` binds what an operation produces. |
| `close`, `normalize`, `intro`, `enumerate` | Explicit proposition tactics. |
| `sorry` | Dev-only proof hole `sorry()`. It parses only under `click verify --allow-sorry`; see [Dev-only proof hole](../cli/verify.md#dev-only-proof-hole). A user-defined tactic may not take the name. |
| `known`, `solve`, `assumption` | Retired tactic names. Write `close()` or `close() using { ... }` with selected premises. |
| `auto`, `arithmetic`, `execute`, `execute_until` | Removed tactic names. The parser refuses each with a diagnostic that names its replacement: the omitted proof for `by auto();` and `close();` for a written `auto();`; `close() using { ... }` for `arithmetic() using { ... }` and `close() using {}` for bare `arithmetic()`; the implicit tail, or `step_until(function.exit)` to work at function exit, for `execute()`; and `step_until` for `execute_until`. |
| `close_invariants` | Retired loop tactic, still reserved. The parser rejects it with `` `close_invariants` is retired ``; a loop's back edge now closes each bundle member with `close()`, helped by `have` facts proved before it. |
| `split`, `left`, `right` | Retired tactic names. Unless a user-defined tactic has the name, the parser rejects each with a diagnostic that names `close()`. |
| `preserve` | Preserve a selected read or its definedness across an explicitly separated region footprint. |
| `rewrite`, `instantiate`, `induct` | Equality, quantifier, and induction tactics. |
| `as`, `else`, `ensuring`, `then` | Names and branches inside structural proof forms. `as` also writes numeric and pointer casts (including `as float` and `as double`) and introduces the target contract's proof instances on an `executes` conclusion. |
| `function`, `loop`, `region`, `statement`, `call`, `test`, `assignment`, `read`, `read_event`, `back_edge`, `entry`, `exit` | Program-region selectors and explicit point suffixes. Append `.entry` or `.exit` to name a region boundary. `region(N)` is the `N`th atomic region, one `step()` crosses; `statement(i)` is a statement as written, and a chain continues it with `.statement(j)` and ends it with `.region(j)`, `.call(f, j)`, `.test()`, `.assignment(x, j)` or `.read(j)`. Unchained `assignment(local, N).entry` and `read(N).entry`, and `loop.back_edge` or `loop(i).back_edge`, are execution targets only. The suffix `.read_event(i).result` selects a completed volatile observation within an atomic region; it is not a point or execution target. |
| `termination` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `termination_local` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `termination_strict` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `termination_body` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `termination_returns` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `termination_divergence` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `termination_callbacks` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `strict` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `normal` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `check_termination_local` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `check_termination_component` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |
| `check_termination_callbacks` | Program termination proof syntax; see [termination proofs](index.md#program-termination-proofs). |

See [Tactics](../tactics/index.md) for tactic syntax and classification, and
[Core tactics](../tactics/index.md#core-tactics) for the ones a hand-written
proof needs; the other tactic words are specialized or expansion output. A word
listed here isn't necessarily valid in every identifier or expression
position; the construct entry defines its allowed context.

## File-level declarations

The following schematic grammar uses `...` for content defined on the linked
language-reference page:

```text
click-file       := item*
item             := import-declaration
                  | verifying-declaration
                  | target-declaration
                  | algebraic-declaration
                  | predicate-declaration
                  | function-declaration
                  | resource-declaration
                  | theorem-declaration
                  | named-contract-declaration
                  | c-function-contract
verifying-declaration := "verifying" string-literal ";"
import-declaration    := "import" (string-literal | library-path) ";"
library-path          := "click" ("::" identifier)+
qualified-name        := ("click" "::")? identifier ("::" identifier)* "::" identifier
target-declaration    := ("target" | "mode") string-literal ";"
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
| 5 | atoms, predicate calls, comparisons, `bool` values | Not applicable |

Thus `p implies q implies r` means `p implies (q implies r)`, while `p or q
or r` means `(p or q) or r`. Use parentheses whenever grouping carries the
explanation. A `Bool` value written alone as an atom, such as `flag` or a
call `f(x)` of a `Bool` function, means `value == true`; see
[Booleans](index.md#booleans).

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

Comparisons form propositions rather than contract expressions, so they bind
looser than every operator in this table. C binds `==`, `!=`, `<`, `<=`, `>`
and `>=` tighter than `&`, `^` and `|`, so a comparison operand whose
outermost operator is `&`, `^` or `|` must be parenthesized: `x & 1 == 0` is
refused and `(x & 1) == 0` is accepted
(`mdtests/bitwise_comparison_operand_needs_parentheses.md`,
`mdtests/parenthesized_bitwise_comparison_operand_is_accepted.md`). Rust binds
`&`, `^` and `|` tighter than comparisons, as Click does, so a sidecar that
verifies Rust is exempt. Shifts and arithmetic group the same way in C and
Click and need no parentheses. See
[Propositions](index.md#propositions) for their syntax and typing rules.

## Algebraic datatypes

The algebraic-datatype slice supports generic, specification-only
sum-of-products declarations as first-class Click types. A
constructor of a generic datatype may leave out its type arguments where its
arguments or its position fix them (see
[Constructor type arguments](#constructor-type-arguments)); every later check,
and the kernel, sees the fully applied constructor. Pure functions, predicates,
and theorems may receive arbitrary algebraic values, pure functions may return
them, and an exhaustive `match` may inspect an unknown variant and return a
common C or algebraic type. An `if` whose branches are values of one datatype
is an algebraic value, `if list::contains(xs, x) { xs } else { List<T>::Cons(x,
xs) }`, in definitions and contract clauses alike; branches of two datatypes, or
one algebraic branch and one that is not, are refused. The kernel term keeps
the condition and both branches; a constant condition or two equal branches
leave one branch, so `unfold` followed by `close() using` the condition or
its negation selects a branch
([`algebraic_conditional_inserts_into_a_generic_list.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_conditional_inserts_into_a_generic_list.md),
[`algebraic_conditional_call_results_select_a_branch.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_conditional_call_results_select_a_branch.md),
[`algebraic_conditional_branches_have_one_type.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_conditional_branches_have_one_type.md)).
Like a scalar `if`, it is outside the forms a termination measure may read.

Pure function definitions check every return branch against the declared result
type, including definitions with no callers. C-valued returns use the existing
numeric conversions and null-pointer-constant rule; a pointer is not an integer
return value. Bool results require bool values rather than implicit truth tests.

A model field declared `struct tag*` retains its nominal pointee class.
Constructing the model requires a null pointer or checked evidence that the
pointer's original object class is `struct tag`; matching the model recovers
that evidence. A pointer proved equal to the typed identity can use that
evidence in the current context. Pure helper parameters declared `struct tag*` require the same
evidence at calls. Helper bodies check their model constructors and calls
against the declared input types. A pure function returning `struct tag*` must
also establish that its body returns null or a pointer with that original
object class. Calls use this checked return type, including recursive calls;
recursive definitions still require the existing termination check. Untyped
and generic pointer getters preserve evidence from their actual return sources.
A destination cast cannot manufacture original-class evidence. C access
typing retains its existing declaration metadata separately. Memory access
still requires the relevant resource permissions.

A model field, pure-helper parameter, or specification expression binding
such as `(let pointer: void* = p; pointer)` accepts an object pointer through
implicit coercion. Its carrier changes to `void*`, preserving
its provenance, bounds, qualifiers, and object-type evidence. Opaque helper
calls and unfolded bodies use this same argument conversion. Function pointers
are excluded. An authored `p as (void *)` remains an explicit cast and selects the
root view according to C cast semantics. Address-only models should use `void*`
without inserting explicit casts that would change saved pointer views. See
`mdtests/model_pointer_void_helper_preserves_selected_view.md` and
`mdtests/a_saved_pointer_link_keeps_its_bounds_through_an_outer_alias_update.md`.

The written C contract is the complete callable interface. Typed model
constructors and typed pure-helper calls in its clauses determine the required
original object classes of its input pointers. For example,
`ensures held.model == NodeRef::At(p)` exposes the nominal type required of
`p`. Imported, recursive, and completed calls check the same declaration-derived
requirements. Contract value parameters carry these requirements too.
A proof cannot silently add a type precondition by choosing `NodeRef::At(p)`
while proving only an abstract output and `ensures true`. It must obtain type
evidence from the declared inputs, owned model fields, or actual declared and
allocated objects. Ordinary C casts and address-only return contracts keep
their existing behavior; a C pointer declaration alone supplies access typing,
not the stronger original-object evidence needed by a model constructor.

A pointer return also retains the nullable object class exposed by a direct
typed use of `result` in a postcondition, either unconditionally or under the
exact guard `result != 0`. Imported and opaque calls use that declaration-backed
guarantee. The function's own proof must establish it on its actual return;
its C return declaration alone supplies none. Uses under other guards and
branching expressions do not establish an unconditional return class.

Opening a held resource recovers the nominal argument requirements of the
logical calls in its active selected body. Folding must establish those
requirements; an empty resource or an inactive body confers no pointer type.
The recovered requirements are explicit scoped facts, independent of opaque
call interning and of C access permissions.

A loop invariant does the same at the loop head. Entry and every back edge
lower each invariant with ordinary lowering, so a typed helper call or model
constructor there must find evidence for its pointer arguments, or the
invariant cannot hold. The head then assumes those requirements for the fresh
values of reassigned locals, as `is_a<T>(p)` facts beside the
invariant. In `while (parent != 0) { ...; parent = rb_parent(node); }` with
`invariant ctx_node_is(c.model, parent) == 1`, the head types `parent`, and
each back edge must show that the new `parent` has class `struct rb_node`
(here, equality with a typed model field). See
`mdtests/a_loop_invariant_supplies_its_typed_call_domains_at_the_head.md` and
`mdtests/a_loop_invariant_typed_call_domain_must_hold_at_the_back_edge.md`.
A `branch ensuring` or `match ... ensuring` fact does the same at its join:
every arm lowers it with ordinary lowering, so the join assumes its typed
calls' requirements for the joined values and exports their `is_a<T>(p)`
facts beside it. See
`mdtests/a_branch_interface_supplies_its_typed_call_domains_at_the_join.md` and
`mdtests/a_branch_interface_typed_call_domain_must_hold_in_each_arm.md`. When
the loop head cannot assume an invariant at all, the refusal names it by
position and says whether it had no reading there or contradicted the
invariants before it.

### Type evidence

`is_a<T>(p)` states that the object `p` points to is a `T`, where `T` is a
struct type `struct S` or a pointer to one, `struct S*`. Like `load<T>(p)`, it
takes the object's type, not the pointer's. It is the fact Click records when
it learns a pointer's object type: opening a resource whose body calls a
typed function on the pointer, a loop head or branch join that assumes a typed
call's domain, or a typed parameter. A proof can state it or cite it, and it
holds only where that evidence exists:

<!-- verified-example: mdtests/is_a_holds_after_opening_a_typed_resource.md -->
```click
void keep(struct node* p) {
    owns held: token(p);
    ensures held.model == old(held.model);
} by {
    unfold(held);
    step();
    have is_a<struct node>(p) by close();
    let held = fold(token(p), { model: old(held.model) });
}
```

Before the token is opened, `is_a<struct node>(p)` is not known
(`mdtests/is_a_needs_type_evidence.md`), and evidence for `struct node` is
not evidence for `struct node*` (`mdtests/is_a_names_the_type_of_the_evidence.md`).

A `malloc` or `calloc` result bound directly to a complete struct pointer
establishes that struct's class when the checked allocation size contains
the object and the allocator guarantees its alignment. The success branch
records the class on both the pointer and its storage; the failure branch is
null. Insufficient storage establishes no class. Casting an existing object,
including an allocated object of another struct type, preserves its original
class. This does not initialize `malloc` storage or grant additional access
permissions.

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
        let ih = induct(xs);
        match xs {
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

### Constructor type arguments

`List::Cons(x, List::Nil)` with `x: int32` means
`List<int32>::Cons(x, List<int32>::Nil)`. Before any checking, a constructor
that leaves out its type arguments takes them from one of two places:

- Its own arguments, by their declared types: a declaration parameter, the
  binder of a `match` arm or of a proof `match` arm (typed from
  its scrutinee), a quantifier binder, a typed `let`, a resource field,
  another constructor whose type is known, or a pure-function call's result.
- The type its position expects: a pure function's result type, the
  parameter of the function, predicate or theorem it is passed to (once the
  call's other arguments fix that parameter's type arguments), the field of
  an enclosing constructor, the other side of `==` or `!=`, or a `let` with a
  written type. A `match`, `let` or `old(...)` passes the expected type on to
  its result.

Nothing else is consulted, and no type is guessed: a bare integer literal
fixes nothing, and names a proof introduces by `intro`, `obtain`, a proof
`let` or a step are not read; one that reuses a declaration parameter's name
is read as that parameter, and a type that does not fit is then refused by
the ordinary type check. When neither place fixes the arguments the
constructor is refused with the written form to use, as in
`mdtests/constructor_type_arguments_that_nothing_fixes_are_refused.md`,
`mdtests/a_proof_constructor_whose_type_nothing_fixes_is_refused.md` and
`mdtests/a_generic_call_on_constructors_nothing_types_is_refused.md`. In
`unfold(list::append(List<int32>::Nil, List<int32>::Nil))` both arguments must
be written: neither the call nor its arguments fix `T`. The written form is
accepted everywhere.

<!-- verified-example: mdtests/constructor_type_arguments_are_inferred.md -->
```click
function singleton(x: int32) -> List<int32> {
    List::Cons(x, List::Nil)
}

theorem append_nothing(xs: List<int32>) {
    ensures list::append(List::Nil, xs) == xs by {
        unfold(list::append(List::Nil, xs));
        close();
    }
}
```

Constructor equality is structural and checked against the resolved datatype
schema. Different variants are disjoint; an assumed equality between them is
a contradiction. Equality of every corresponding field proves equality of
two applications of one constructor (congruence), and an exact equality of
such applications exposes equality only at the same field position
(injectivity). `close()` can select these rules, expanding congruence to explicit
`rewrite` steps and injectivity to checked `have ... by close();` steps.

Pattern arms must name every variant exactly once, use the declared field
arity, and keep field bindings local to the arm. Generic arguments and fields
may be modeled C types or other fully applied algebraic types; nested generic
applications such as `Holder<Maybe<int32>>` are supported. A field may be a
pointer to a type parameter, `Span(T*, uint64)`: at an instance it is the
element's pointer type, `uint8*` for `Span<uint8>`, and in a generic
declaration it stays `T*`
([`a_spec_enum_field_points_to_its_type_parameter.md`](https://github.com/clicklang/click/blob/master/mdtests/a_spec_enum_field_points_to_its_type_parameter.md)). Nested fields stay
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
supported regular form must preserve the enclosing type parameters
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
let m: Maybe<int32> = Maybe<int32>::Some(value);
m
...
let m = wrap(value);
m
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
`let ih = induct(value);` followed by
`match value { Type::Variant(fields) => { ... } ... }`; it requires one
arm per constructor and permits `ih(field)` for immediate fields of the same
recursive datatype. Mutual induction across distinct datatype families is not
generated. Reusing one constructor refinement across repeated matches is
tracked separately in the algebraic match path-correlation issue.

## Tuples

Tuples have Rust's syntax and meaning ([design](https://github.com/clicklang/click/blob/master/design/tuples.md)).
A tuple type is `(A, B)`, `(A,)` or `()`, with up to 12 components of any
Click value type, including `Integer`, spec enums and other tuples. A value is
`(a, b)`, `(a,)` or `()`; `(a)` is `a` parenthesized. `t.0` is a component,
`let (a, b) = t; body` and the match arm `(a, b) => body` bind every
component, and `==` is componentwise:

<!-- verified-example: mdtests/tuples_construct_project_and_compare.md -->
```click
function swap(p: (int32, int32)) -> (int32, int32) {
    (p.1, p.0)
}
```

A tuple is a built-in datatype of one constructor, so constructor equality,
`match` and a proof `match` apply to it as to a `spec enum`. A projection
is a one-arm match: `(x, y).0 == x` closes with `close()`, and
`(x, y) == (u, v)` gives `x == u`. A projection of a projection needs its
inner step, `have ((x, y), z).0 == (x, y) by close();` and a `rewrite`. A
proof `match t { (a, b) => { ... } }` introduces `t == (a, b)`, which proves
surjective pairing, `swap(swap(p)) == p` in the example. Printed facts and
expanded proofs spell tuples as written: `(A, B)`, `(a, b)` and `t.1`.

A projection needs its receiver's type: a parameter, a typed `let`, a call
result, a constructed tuple or a match binding of one. A projection of a
non-tuple, an index past the last component, a one-component tuple without
its trailing comma, and a tuple whose components' types nothing fixes are
refused. Patterns bind names only; they do not nest, and a destructuring
`let` takes no type annotation. A Rust `fn` signature, in a sidecar or an
interface file, cannot yet take or return a tuple: tuple program values are
refused by name
(`rust_fn_signatures_refuse_tuple_program_values` in
`src/surface/tests/surface_syntax.rs`).

## Specification sequences

`[a, b, c]` is an immutable finite specification sequence. Its elements must
have one compatible C scalar or data-pointer type. `[]` is the empty sequence,
and `left ++ right` concatenates two compatible sequences without allocating C
memory or granting memory authority. Sequence values support `==`, `!=`, and
the proposition `element in sequence`; ordering comparisons are rejected.

Concatenation is associative and `[]` is its left and right identity. Sequence
equality compares elements rather than concatenation-tree shape, preserving
order and multiplicity.

`old(...)` and `at(...)` evaluate every element at the selected point,
so a contract can relate current array cells to their exact entry order:

<!-- verified-example: mdtests/c_named_contract_sequence_refinement.md -->
```click
ensures [cells[0], cells[1]] == old([cells[1], cells[0]]);
```

Literal sequence values appear in equality and membership propositions. The
standard library also supplies the algebraic `List<T>` with `Nil`, `Cons`,
append, and membership. The literal operators are not defined over that
library type, and sequences have no general indexing and no projection of a
symbolic memory range.

## C-fragment precedence

C fragments use C-like precedence. From lowest to highest:

| Precedence | Operators | Associativity |
| --- | --- | --- |
| 1 | `\|` | Left |
| 2 | `^` | Left |
| 3 | `&` | Left |
| 4 | `<`, `<=`, `>`, `>=`, `==`, `!=` | Left |
| 5 | `<<`, `>>` | Left |
| 6 | `+`, `-` | Left |
| 7 | `*`, `/`, `%` | Left |
| 8 | supported unary operators | Prefix |
| 9 | calls, indexing, member access | Left, postfix |

Conjunction and disjunction are the proposition connectives `and` and `or`.
The C logical operators `&&` and binary `||` are refused in that syntax.
A nullary specification lambda uses `||` for its empty parameter list.

This table describes the parser, not all of ISO C. The normative set of types,
statements, and operators that Click accepts is in [Supported C](c.md).

## Specification lambdas

A lambda is a lexical specification value. Each parameter and the result have
an explicit type: `|x: Integer| -> Integer { x + 1 }`. Call a lambda value with
ordinary application syntax, `f(value)`, or apply an expression directly,
`(|x: Integer| -> Integer { x + 1 })(3)`. Arguments are bound simultaneously,
so a parameter never captures a name in another argument. A nullary lambda
can be applied as `(|| -> Integer { 7 })()`.

Expression-local `let` bindings can name and alias lambdas. A local annotation
uses `fn` to write the function signature, as `fn(Integer) -> Integer`;
otherwise the literal determines its type. Captures retain their lexical binding across
later shadowing. Lambdas are nonrecursive values: the name a `let` introduces
is not in scope in its initializer.

<!-- verified-example: mdtests/typed_lambdas.md -->
```click
function captured(offset: Integer) -> Integer {
    let add = |x: Integer| -> Integer { x + offset };
    let offset: Integer = 100;
    add(2)
}
```

Lambdas support `Integer`, `Bool`, 8–64 bit integers, and
floating-point scalar parameters and results. The result type checks the body even when the lambda
is unused. Lambdas may capture values (including pointers) and other local
lambdas, read memory, and call memory-reading specification functions.
Capturing a pointer captures its value, not a memory state. Reads and
current-state observations in the body use the state selected at application;
applications retain the existing read-permission and definedness obligations,
including beneath range-membership guards. Constructing an unused lambda
requires no read permission. `old` and `at` inside lambda bodies are refused;
select a state around the application instead, as `old(read(0))`. A value
loaded before construction can be captured separately. Capturing a pointer
grants no memory permission: proving `defined(read(i))` still requires a
view covering the selected cell.

Specification functions accept function parameters as described below.
Function-valued declaration results, function equality, function-valued theorem
parameters, and algebraic lambda parameters/results are not supported yet.
A lambda may also return `Prop`, as described below. `.fold`, `.all`,
and `.any` accept lambda values.

Applications elaborate to typed lexical value bindings, using existing kernel
terms. They introduce no higher-order proof search or automatic extensionality.

<!-- verified-example: mdtests/memory_reading_lambdas.md -->
```click
function typed_sum(p: int32*, lo: int32, hi: int32) -> Integer {
    let add = |acc: Integer, i: int32| -> Integer { acc + to_integer(p[i]) };
    (lo..hi).fold(0, add)
}
```

### Proposition-valued lambdas

`Prop` is a specification proposition, distinct from a C `Bool`. A lambda
returning `Prop` parses its body as a proposition: comparisons, connectives,
and quantifiers retain their logical meaning. Application asserts that
proposition when written in a clause. A `Prop` is refused in a scalar value slot such as a `Bool` let or function
argument; propositions have no arithmetic or equality. A `Bool` function
body retains its existing logical-body syntax, which reads a proposition
as `if P { true } else { false }`.

<!-- verified-example: mdtests/proposition_lambdas.md -->
```click
theorem direct_proposition_lambda(x: Integer) {
    ensures (|value: Integer| -> Prop { value == value })(x) by close();
}
```

`fn(Integer) -> Prop` denotes a proposition-valued lambda's signature.
`prop { P }` constructs a proposition value directly; local `let` bindings
can name that value or a proposition application. Lambda arguments remain
scalar or `Integer` values: lambda parameters of proposition or function type
and function-valued declaration results are not supported yet. Named
propositions may use `predicate` or a transparent `function ... -> Prop` helper.
A `Prop` lambda uses the same application-state reads and body state
restriction as scalar-valued lambdas; it may call named predicates.

### Function parameters in specification functions

A specification function may take a callback with an explicit, fixed
`fn(...) -> ...` signature. Its body can apply, alias, and forward that value,
including passing it to a range method. The callback's parameters are scalar
or `Integer`; its result may also be `Prop`. Signatures match exactly.
The body is checked even if the function is never called.

<!-- verified-example: mdtests/specification_function_parameters.md -->
```click
function twice(f: fn(Integer) -> Integer, x: Integer) -> Integer {
    f(f(x))
}
```

At a call site, each callback must resolve to a lambda literal or local alias.
For example, `twice(|x: Integer| -> Integer { x + 1 }, 3)` denotes `5`.
The frontend specializes the selected body with typed lexical argument
bindings. Captures and application-state memory reads follow the lambda rules
above; specialization introduces no kernel function-value form or proof search.

Logical adapters return `Prop`, retaining the proposition's quantifiers:

<!-- verified-example: mdtests/specification_function_parameters.md -->
```click
function every(predicate: fn(int32) -> Prop, lo: int32, hi: int32) -> Prop {
    (lo..hi).all(predicate)
}
```

A `Prop` function parses its body as a proposition and elaborates its calls
directly to that proposition. Ordinary `intro` and `witness` rules therefore
apply to its returned quantifier. Scalar and `Integer` helpers retain the
usual `unfold(f(args))` syntax. Arbitrary-function theorem parameters,
function-valued results, function equality, and recursive callback-taking
functions remain unsupported. A named specification function is not implicitly
a callback value; wrap its call in a typed lambda.

## Ranges and binders

`lo..hi` denotes the half-open integer range whose elements satisfy `lo <= k <
hi`. A range can introduce a binder through `.all`, `.any`, or `.fold`:

<!-- verified-example: mdtests/range_helpers_over_memory.md -->
```click
(lo..hi).all(|k| { p[k] == 0 })
(lo..hi).any(|k| { p[k] == needle })
(lo..hi).fold(0, |acc, k| { acc + p[k] })
```

### Range predicates

`(lo..hi).all(predicate)` and `(lo..hi).any(predicate)` accept a lambda
with exactly the signature `fn(Index) -> Prop`, where `Index` is `int32`
or `uint64`, as selected by the bounds. The predicate can be a typed
literal or a local value/alias with lexical captures. A `Bool` result is
refused; the predicate is a proposition, including for an empty range.
The existing unannotated `.all(|k| { P })` and `.any(|k| { P })` shorthands
remain supported, including guarded memory reads.

<!-- verified-example: mdtests/proposition_lambdas.md -->
```click
theorem existential_range_lambda(lo: int32, hi: int32) {
    let same = |x: int32| -> Prop { x == lo };
    requires lo < hi;
    ensures (lo..hi).any(same) by {
        witness(lo);
        close();
    }
}
```

The value forms use `item` as the written range binder. An `.any` witness
therefore names `item`. In an `.all` proof, `intro(k) { ... }` binds the
index as `k` and introduces both bounds for the block. Elaborated applications
use the existing
universal/existential range terms and add no proof search.

### Range folds

`(lo..hi).fold(initial, step)` accepts a typed specification lambda value.
The step must have exactly the signature `fn(A, I) -> A`, where `A` is the
accumulator carrier and `I` is the range's index carrier. The initial value
must have carrier `A`. A step can be a literal, a local binding or alias, or
an expression producing a lambda. Captures retain their lexical bindings.

<!-- verified-example: mdtests/lambda_folds.md -->
```click
function lambda_total(lo: int32, hi: int32, offset: Integer) -> Integer {
    let step = |acc: Integer, k: int32| -> Integer { acc + to_integer(k) + offset };
    let alias: fn(Integer, int32) -> Integer = step;
    (lo..hi).fold(0, alias)
}
```

The supported carriers remain unchanged: an `Integer` accumulator can use
`int32`, `uint64`, or `Integer` indices; an `int32` accumulator requires
`int32` indices. A typed step and its initial value are checked even for an
empty range. Applications use the same capture-avoiding elaboration as an
explicit lambda call, and fold laws and machine arithmetic guards are unchanged.

The unannotated shorthand `.fold(initial, |acc, k| { body })` remains
supported and infers its carriers from the range, initial value, and body.
Both shorthand and typed steps support guarded memory reads. Their read
permissions and definedness obligations are checked under the same range
guards.

Quantifiers use an explicitly typed binder:

<!-- verified-example: mdtests/proposition_connectives_quantifiers_and_old.md -->
```click
forall (x: int32) { x == x }
exists (x: int32) { x == value }
```

Binder scope is the body between braces. Renaming a bound variable doesn't
change the proposition or expression it denotes.

Expansion gives an introduced proof value an ordinary lexical name.
For example, `intro(x) { ... }` introduces the value for a universal goal.
References use `x` within its scope. Expansion chooses names that avoid
the surrounding source bindings.

`(expression : Integer)` supplies mathematical integer context without a
binding. It is also used by expansion when an integer result has lost the
operand that originally supplied its type context.

## Proof syntax

Write `if P { ... } else { ... }` or
`if P ensuring { ... } then { ... } else { ... }`.
A C `branch` has labeled arms in a block:
`branch { true => { ... } false => { ... } }`.
Its optional join interface precedes that block:
`branch ensuring { ... } { true => { ... } false => { ... } }`.

A proof is omitted, written as a single tactic call such as `by close();`, or
written as a `by { ... }` block of tactic statements. Tactic
arguments use the expression and proposition forms documented for that tactic. The exhaustive surface-syntax inventory is in
[Tactics](../tactics/index.md).

One tactic carries syntax beyond an argument list. A `step` on an ordinary C
call writes the call as it appears in the source, maps the callee's instance
binders to the caller's instances, and introduces a produced instance with
`let`. Any `step` form may end with proofs of the obligations its fast path
leaves open: a plain `by` for exactly one, or a block of `requires` entries.

```text
step-tactic    := step-head step-proof
step-head      := ("let" output-pattern "=")? "step" "(" step-args? ")"
step-args      := contract-name ("(" resource-args ")")? | c-call "," binder-map
binder-map     := "{" (identifier ":" identifier
                   ("," identifier ":" identifier)* ","?)? "}"
step-proof     := ";" | "by" proof-body | "{" requires-entry+ "}"
requires-entry := "requires" (identifier ":")? proposition "by" proof-body
proof-body     := tactic-call ";" | "{" tactic-statement+ "}"
```

Omitting a proof requests smart proof construction, and so does the implicit
tail that ends every written script. Smart
search can advance proof state only through checked operations. Use
[`click expand`](../cli/expand.md) to replace expandable smart proof sites with
the corresponding explicit proof steps; Click verifies the complete rewritten
source.
