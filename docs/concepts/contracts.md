# Contracts

A Click contract describes a C function from the outside.

The main clauses are:

```text
let name [: type] = expression;
let name: type where proposition;
requires ...
owns ...
views ...
ensures ... by ...
```

Initial proofs mostly use `requires` and `ensures`. Memory proofs also add
`owns` and `views`.

## Local names

A contract can define immutable local names:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
let max: int32 = 2147483647;
let expected: int32 = x + 1;

requires x < max;
ensures result_value: result == expected;
```

These `let` bindings are Click-side abbreviations. They do not add runtime C
variables and they are not mutable proof state. A type annotation is optional
when Click can infer the intended value shape from use, except that arithmetic
on a machine value needs one: `let expected: int32 = x + 1;` is C's sum and
`let expected: Integer = x + 1;` the exact one
([Integer specification arithmetic](../reference/language/index.md#integer-specification-arithmetic)).

A contract can also bind an immutable witness with `let ... where`:

<!-- verified-example: mdtests/contract_let_where.md -->
```click
let k: int32 where k == x;

ensures result_matches_witness: result == k by {
    step_until(function.exit);
    witness(x);
}
```

This is proposition-level sugar for an existential witness. The `where`
condition and the later proposition are proved together. The witness type is
required explicitly.

## Requirements

A `requires` clause is a precondition:

<!-- verified-example: mdtests/contract_clause_forms.md -->
```click
requires x >= 0;
requires x < 2147483647;
```

Click may assume requirements when proving the function. Callers are responsible
for satisfying them.

Requirements are also where simple C safety facts often live. For example,
`requires x < 2147483647;` makes `x + 1` safe from signed overflow.

Resource verbs provide resource facts alongside pure requirements:

<!-- verified-example: mdtests/contract_clause_forms.md -->
```click
views p[0..1];
consumes p[1..2];
```

These give the verifier permission to check external memory accesses. `views`
permits loads; an owned element permits both loads and stores.
`owns a[i]` and `views a[i]` cover one element at that index, using the
element type and byte width of `a`, including 64-bit integers. They grant
no access to neighboring elements.
Resource facts are carried separately from pure facts.
[Resources and memory permissions](resources.md) covers transfer through
function calls and the distinction between viewability and authority.

Requirements are written without fact labels:

<!-- verified-example: mdtests/contract_clause_forms.md -->
```click
requires x > 0;
```

To use an existential requirement in a proof, state its proposition in
`let k = obtain(exists (x: Type) { ... });` after it is available.

## Guarantees

An `ensures` clause is a postcondition:

<!-- verified-example: mdtests/contract_clause_forms.md -->
```click
ensures result == x + 1;
ensures result > x;
```

Each `ensures` clause is proved separately. A function can have several
guarantees, and each guarantee can use a different proof clause.

Postconditions are conditional on return. A function that runs forever has no
return state at which an `ensures` clause could fail. This does not make its
body unchecked: every finite execution prefix must still avoid checked
undefined behavior, respect resource authority, and write only within its
declared effect footprint.

The name `result` means the function's return value.

Callback contracts can also produce resources indexed by `result`. For example,
an acquisition callback can return null with no cell, or a nonnull pointer with
ownership of that cell. After `step(ContractName)`, an explicit proof case on
the returned pointer permits unfolding the corresponding resource branch.
The same unfolding works without a case when the contract already establishes
the guard. The repository tests `mdtests/c_contract_executes_acquire.md` and
`mdtests/c_contract_executes_acquire_nonnull.md` demonstrate both forms.
Returned ownership does not by itself establish that the allocation is fresh;
writes must still satisfy the caller's declared effect footprint.

Guarantees can also be labeled:

<!-- verified-example: mdtests/contract_clause_forms.md -->
```click
ensures incremented: result == x + 1;
```

Guarantee labels identify postcondition claims in diagnostics and proof scripts;
they do not name facts.

A guarantee also decides whether a function can be passed where a named
callback contract is required. Click checks behavioral refinement: the named
requirements must imply the function's, and the function's guarantees must
imply the named ones. The check is exact rather than a search: it admits a
documented list of proposition classes, and a contract outside that list is
refined by an explicit theorem instead. See
[Automatic formation at `&f`](../reference/language/index.md#automatic-formation-at-f)
for the list and for the pairing a contract with resource handles
needs.

A named contract's resource proof parameters use the C parameter types declared
in its C declaration, including their struct field layouts. Reading a pointer field to
index a resource still needs a `views` or `owns` clause for that field.

In an `executes` theorem, the executed function's parameters are available in
the guarantee's proof block with their declared struct types. Field paths,
including nested fields, use those layouts in `have` propositions and other
proof steps. This scope ends with the guarantee; it grants no memory authority.

## Write footprints

Memory-modifying functions declare the memory they own:

<!-- verified-example: mdtests/copy_n_segment_invariant.md -->
```click
views src[0..n];
owns dst[0..n];
```

Ownership says which parts of memory may be written; a view permits reads only.
There is no separate effect clause: the owned memory *is* the write footprint,
and a store outside it fails at the store. Unlike a return postcondition, a
write footprint constrains finite writes even on an execution that later runs
forever.

The footprint is derived by the verifier from the resource clauses, with
owned composites opened through their definitions; nothing lowered from the
contract text is a second copy of it. A loop that declares its own `owns`
clauses gets its footprint the same way at loop entry, and a loop without a
declaration inherits the function's.

## Proof clauses

The `by` clause says how a guarantee is proved:

<!-- verified-example: mdtests/contract_clause_forms.md -->
```click
ensures result == 0;
ensures result == x by { step_until(function.exit); close(); }
```

An omitted proof clause runs the function and closes the claim at its exit.
A tactic script starts at function entry: `step_until(function.exit)` steps
through the C to the exit, where `close()` closes the claim. Every script,
like the omitted one, ends with an implicit tail that runs any C the script
left and closes each open goal on every path, so a script holds only the
steps that need proof work and needs no final closer.

A call retains an input proposition for the continuation only when the
incoming checked facts independently prove it. Call-local assumptions of
pending prerequisites cannot supply that evidence. The retained proposition
keeps the pre-call version points of its reads and its model values, so it cannot describe a
cell's new value after a write. This also retains definedness of a checked
resource-count sum; see
`mdtests/solve_defined_count_after_a_zero_summand.md` and the rejected stale-read
case `mdtests/call_checked_input_facts_keep_prestate.md`.
