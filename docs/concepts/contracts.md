# Contracts

A Click contract describes a C function from the outside.

The main clauses are:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
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
let expected = x + 1;

requires x < max;
ensures result == expected by auto;
```

These `let` bindings are Click-side abbreviations. They do not add runtime C
variables and they are not mutable proof state. A type annotation is optional
when Click can infer the intended value shape from use.

A contract can also bind an immutable witness with `let ... where`:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
let k: int32 where k == x;

ensures result == k by {
    execute();
    witness(k = x);
    simp();
}
```

This is proposition-level sugar for an existential witness. The `where`
condition and the later proposition are proved together. The witness type is
required explicitly.

## Requirements

A `requires` clause is a precondition:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
requires x >= 0;
requires x < 2147483647;
```

Click may assume requirements when proving the function. Callers are responsible
for satisfying them.

Requirements are also where simple C safety facts often live. For example,
`requires x < 2147483647;` makes `x + 1` safe from signed overflow.

Resource verbs provide resource facts alongside pure requirements:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
views p[0..1];
consumes p[0..1];
```

These give the verifier permission to check external memory accesses. `views`
permits loads; an owned element permits both loads and stores.
Resource facts are carried separately from pure facts.
[Resources and memory permissions](resources.md) covers transfer through
function calls and the distinction between loadability and authority.

Requirements can be labeled:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
requires positive: x > 0;
```

Labels are useful when a proof script needs to refer to a specific fact.

## Guarantees

An `ensures` clause is a postcondition:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
ensures result == x + 1 by auto;
ensures result > x by auto;
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

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
ensures incremented: result == x + 1 by auto;
```

Labels make diagnostics easier to read and make proof scripts more durable.

A guarantee also decides whether a function can be passed where a named
callback contract is required. Click checks behavioral refinement: the named
requirements must imply the function's, and the function's guarantees must
imply the named ones. That check admits scalar comparisons over current and
function-entry memory, reads of a resource instance's fields on either state,
algebraic equalities, `match` over an algebraic value, and algebraic arguments
to a pure function. It excludes `at(...)`, explicit memory snapshots,
counted-resource populations, and range folds, which need an explicit
refinement theorem instead. When the contract declares resource proof
parameters, the pairing between them and the function's binders must be forced
— one binder per parameter, same resource family, equal arguments — and a
refusal prints the theorem that states the pairing.

## Write footprints

Memory-modifying functions declare the memory they own:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
views src[0..n];
owns dst[0..n];
```

Ownership says which parts of memory may be written; a view permits reads only.
There is no separate effect clause: the owned memory *is* the write footprint,
and a store outside it fails at the store. Unlike a return postcondition, a
write footprint constrains finite writes even on an execution that later runs
forever.

## Proof clauses

The `by` clause says how a guarantee is proved:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
ensures result == 0 by auto;
ensures result == x by simp;
```

Omitting the proof clause currently uses the default prover, `auto`, but writing
the proof explicitly is clearer in examples.
