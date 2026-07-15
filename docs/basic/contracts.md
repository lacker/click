# Contracts

A Click contract describes a C function from the outside.

The main clauses are:

```click
let name [: type] = expression;
let name: type where proposition;
requires ...
ensures ... by ...
immutable ...
mutable ...
```

Beginner proofs mostly use `requires` and `ensures`. Memory proofs later add
`immutable` and `mutable`.

## Local Names

A contract can define immutable local names:

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

```click
let k: int32 where k == x;

ensures result == k by {
    execute_rest();
    witness(k = x);
    simp();
}
```

This is proposition-level sugar for an existential witness. The `where`
condition and the later proposition are proved together. The witness type is
required explicitly.

## Requirements

A `requires` clause is a precondition:

```click
requires x >= 0;
requires x < 2147483647;
```

Click may assume requirements when proving the function. Callers are responsible
for satisfying them.

Requirements are also where simple C safety facts often live. For example,
`requires x < 2147483647;` makes `x + 1` safe from signed overflow.

Resource verbs provide resource facts alongside pure requirements:

```click
views p[0..1];
consumes p[0..1];
```

These give the verifier permission to check external memory accesses. `views`
permits loads; an owned element permits both loads and stores.
Resource facts are carried separately from pure facts. The intermediate
[Permissions](../intermediate/permissions.md) chapter covers transfer through
function calls and the distinction between loadability and authority.

Requirements can be labeled:

```click
requires positive: x > 0;
```

Labels are useful when a proof script needs to refer to a specific fact.

## Guarantees

An `ensures` clause is a postcondition:

```click
ensures result == x + 1 by auto;
ensures result > x by auto;
```

Each `ensures` clause is proved separately. A function can have several
guarantees, and each guarantee can use a different proof clause.

The name `result` means the function's return value.

Guarantees can also be labeled:

```click
ensures incremented: result == x + 1 by auto;
```

Labels make diagnostics easier to read and make proof scripts more durable.

## Effects

Memory-modifying functions also use frame clauses:

```click
immutable src[0..n] by frame;
mutable dst[0..n] by frame;
```

These say which parts of memory are preserved or may be written. They are
introduced later, after pointer loadability and aliasing.

## Proof Clauses

The `by` clause says how a guarantee is proved:

```click
ensures result == 0 by auto;
ensures result == x by simp;
```

Omitting the proof clause currently uses the default prover, `auto`, but writing
the proof explicitly is clearer in examples.
