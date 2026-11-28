# Tuples

Status: T1 implemented (specification and contract tuples). T2 and T3 are
planned below.

Click had no tuple type. A Rust program's tuples were read as special cases
in the importer (`split_at` destructuring through `MirLocalId::SliceComponent`,
`enumerate` pairs, checked-arithmetic pairs), and a contract could not name a
pair at all. This record adds tuples to Click with Rust's syntax and meaning,
in three steps.

## Design check

```text
Design check
- Part: frontends (fast): Surface parsing, declaration expansion, printing.
  No kernel, fact-store, decision or search change.
- Why this part: a tuple is a datatype of one constructor, which the kernel
  already represents, checks and eliminates; only its spelling is new.
- Fast: no new read of any index. Parsing `(a, b)` and `t.0` is linear in the
  text; resolving `t.0` reads the receiver's already-inferred type (the
  existing typed method resolution, one lookup by the receiver); the library
  carries 13 fixed definitions (arities 0..=12), the same per-selection cost
  as any library datatype. Printing a match checks its one arm. No new scaling
  test: no operation's work grows with anything but the written tuple.
- Slow: none. `(a, b).0 == a` needs no search: lowering a match on a
  constructed value selects the arm by construction, as for every spec enum.
- Fact-stable: lowering reads no facts for tuples. A projection lowers to
  the same match term whatever the facts; a known constructor scrutinee is
  selected structurally, as before.
- Failure: a projection on a non-tuple, an out-of-range component, a
  projection whose receiver's type is not known, a one-component tuple
  without its trailing comma, and a tuple in a `fn` signature are refused
  with the written form named.
```

## Syntax and meaning (T1)

| Form | Example | Meaning |
|---|---|---|
| Type | `(int32, uint8)`, `(Integer,)`, `()` | the tuple type of those components |
| Value | `(x, y)`, `(x,)`, `()` | the tuple of those components |
| Projection | `t.0`, `t.1`, `((x, y), z).0.1` | the component at that index |
| Destructuring | `let (a, b) = t; a + b` | binds each component in the body |
| Pattern | `match t { (a, b) => a }` | the same, as a match arm |
| Equality | `(x, y) == (u, v)` | componentwise |

As in Rust, `(a)` is `a` parenthesized and the one-component tuple needs
its trailing comma, `(a,)`. `()` is the unit tuple in specification types
and values. Components may be any Click value type: C scalars and pointers,
`Integer`, spec enums, slices, and tuples. A tuple has at most 12
components, the arity Rust's standard library implements its traits for.

```click
function swap(p: (int32, int32)) -> (int32, int32) {
    (p.1, p.0)
}

theorem construction_and_projection(x: int32, y: int32) {
    ensures (x, y).0 == x by close();
}

theorem equality_is_componentwise(x: int32, y: int32, u: int32, v: int32) {
    requires (x, y) == (u, v);
    ensures x == u by close();
}
```

## Representation

A tuple type of arity `n` is a built-in datatype of one constructor whose
fields are its `n` type parameters. The Click library carries the
definitions of arities 0 to 12 (`src/surface/tuples.rs`), named `(tuple)n`, a
name no declaration can spell, so a program's own `spec enum` cannot collide
with one. The constructor has the same name. So:

- `(a, b)` is the constructor application, its type arguments inferred
  from its components or from the position's expected type, as for
  `List::Cons(x, xs)`.
- `t.i` is the single-arm match `match t { (_0, ..., _n-1) => _i }`. The
  parser reads `t.0` as a method `.0` on `t` (no C field starts with a
  digit), and typed method resolution, which knows the receiver's type,
  rewrites it once the arity is known. A projection of a projection,
  `t.0.1`, reads the inner projection's component type.
- `let (a, b) = t; body` and the arm `(a, b) => body` are the match with
  that arm.

Nothing is new in the kernel. Constructor formation, constructor equality
(congruence and injectivity), match lowering, symbolic case splitting
(`match t { (a, b) => { ... } }` in a proof) and raising all apply to tuples
as to any `spec enum` of one variant.

Projection of a constructed tuple simplifies by construction: lowering a
match whose scrutinee is a constructor selects that arm and binds the
fields, so `(a, b).0` lowers to `a`. A projection of a symbolic tuple `t`
stays the retained match term, which the existing retained-match rewriting
reduces once `t` is known to equal a constructor; a proof `match t` gives
that equality.

In an equality the kernel retains a known-constructor match, as for every
spec enum, and `close()` reduces a retained match whose scrutinee is a
constructor: `(x, y).0 == x` closes. A projection of a projection,
`((x, y), z).0.1`, needs the inner step written,
`have ((x, y), z).0 == (x, y) by close();` and a `rewrite`, because the
retained outer match's scrutinee is a match, not a constructor.

Equality is the datatype's: two constructions are equal exactly when their
components are (injectivity and congruence). Surjective pairing, `t ==
(t.0, t.1)` for a symbolic `t`, holds and is proved by a proof `match t`,
which introduces `t == (a, b)`. `close()` does not yet derive `p == q` from
`p.0 == q.0` and `p.1 == q.1` for two symbolic tuples, even after matching
both; that needs the projection of a matched symbolic tuple to rewrite to
its binding, which is the same gap a one-variant `spec enum` has today.

Known raise-lower audit findings (`click audit raise-lower` on
`mdtests/tuples_construct_project_and_compare.md`): facts that an `unfold`
substitutes a constructed tuple into, and facts a `rewrite` or a smart
rewrite produces over matches, report `differs`, `unraised` or `polarity`.
The same fixture written with a user `spec enum Pair<A, B> { Pair(A, B) }`
on the unchanged verifier reports the same `differs` and `unraised`
findings, so they are pre-existing retained-match defects, not tuple
spellings; they are not fixed here.

## Raising and printing

Every printer spells the tuple datatype `(A, B)`, the constructor `(a, b)`,
a match pattern `(a, b)`, and a single-arm tuple match whose body is one of
its bindings as the projection `t.i` (parenthesizing a compound `t`). Each
spelling parses and lowers to the term it was printed from: binding names
are not part of a kernel term's identity (`BindingNames` compares equal),
so `t.1` and `match t { (a, b) => b }` are the same term. The spelling is
chosen from the term's own structure; no candidate form is tried.

## Departures from Rust

- A Click `match` arm binds names only: tuple patterns do not nest, and
  `(a, b)` in a pattern binds each component to a name. Rust's nested and
  literal patterns are later work.
- A destructuring `let` takes no type annotation; write it on the value,
  `let t: (A, B) = v;`.
- A parenthesized type `(A)` is refused rather than read as `A`.
- Integer literal components take their type from context like every Click
  literal; Rust would default an unconstrained `(1, 2)` to `(i32, i32)`.

## Plan

### T1: specification tuples (this change)

Tuple types in pure function, predicate and theorem signatures and in
Rust interface contract types; construction, projection, destructuring and
tuple match patterns in spec expressions and contracts; type checking
through the existing datatype checks; lowering through the existing
constructor and match lowering; printing and raising. A `fn` signature in a
Rust sidecar or interface file that takes or returns a tuple is refused:
tuple program values are T2.

### T2: tuple program values

A Rust program value of a tuple type is the T1 datatype value. The Rust
importer gives tuple locals, fields and results `ProgramType`s of the tuple
datatype, lowers a tuple aggregate to the constructor and a field read
`t.0` to the projection, and drops the special cases: `split_at`'s
`MirLocalId::SliceComponent` and `slice_pairs` (`charon/split_slices.rs`),
`enumerate`'s pairs (`charon/enumerate.rs`) and the checked-arithmetic pairs
(`charon/panics.rs`). A `fn` signature then accepts a tuple, and the T1
refusal is removed.

### T3: `split_at` as a library contract

`split_at` becomes a library function whose contract returns `(&[T], &[T])`
with `result.0` and `result.1` as the two subslices, and the importer's
`split_at` special case goes away. Per-component ownership in contracts,
`owns *result.0`, which `split_at_mut` needs, is separately approved later
work.
