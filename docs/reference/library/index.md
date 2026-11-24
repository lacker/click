# Click library

The Click library is the public Surface Click API in the
[`library/`](https://github.com/clicklang/click/tree/master/library) modules.
It isn't the Rust crate's internal `pub` API. This page lists it one module
per section.

## Layers

Each library declaration is in one of three layers, and its layer decides
how far it is trusted:

- **Verifier primitives** are part of the language, not the library. The
  abstract resources `mutex_guard`, `mutex_live`, `mutex_use`, `publisher`,
  `subscriber`, `authority` and `allocation`, and
  `__click_constant_p_unknown`, are given their meaning by the kernel or the
  C front end. Their declarations sit in `library/primitives.click` and
  `library/c/builtins.interface.click`, and are documented under
  [verifier primitives](../language/index.md#verifier-primitives) in the
  language reference, not here.
- **Language library interfaces** state what the C, C++ or Rust library the
  verified code calls does, designed as
  [library interfaces](../../concepts/library-interfaces.md) describes. Each
  is an assumed `extern` contract, listed in
  [trust](../../concepts/trust.md#library-interfaces), and it comes with the
  code that uses it, not with a sidecar import. `click::c::string` is written
  in Click below. The C front end builds in the allocator family
  ([heap allocation](../language/c.md#heap-allocation)) and writes the
  literal-format contracts ([formatted output](../language/c.md#formatted-output)),
  and the C++ and Rust importers append the generic contracts of
  `library/cpp/` and `library/rust/core.interface.click`, written out at each called
  instance, and the Rust integer-method contracts of
  `library/rust/integers.interface.click` an import calls. The Rust core-method
  contracts state their results with the `click::rust::` modules below.
- **The specification library** is checked Click: types, pure functions,
  predicates and theorems. A theorem is either proved or a kernel standard
  theorem whose declaration is checked against its kernel builder. The
  `click::rust::vec` axioms are trusted, not proved.

## Modules

| Module | Seen | Layer |
| --- | --- | --- |
| [`click::nat`](#clicknat) | implicit | specification |
| [`click::list`](#clicklist) | implicit | specification |
| [`click::option`](#clickoption) | implicit | specification |
| [`click::result`](#clickresult) | implicit | specification |
| [`click::integer`](#clickinteger) | `import click::integer;` | specification |
| [`click::permutation`](#clickpermutation) | `import click::permutation;` | specification |
| [`click::bytes`](#clickbytes) | `import click::bytes;`, or with `click::c::string` | specification |
| [`click::c::stdarg`](#clickcstdarg) | `import click::c::stdarg;`, or when a contract declares `...args` | C language interface |
| [`click::c::stdio`](#clickcstdio) | `import click::c::stdio;`, or with the projected `<stdio.h>` | C library interface |
| [`click::c::string`](#clickcstring) | `import click::c::string;`, or when the C declares or calls a modeled string function | C library interface and specification |
| [C++ standard library interfaces](#c-standard-library-interfaces), `library/cpp/` (not a module) | when a C++ import calls one of its functions | C++ library interface |
| [`click::rust::i8` ... `click::rust::usize`](#clickrusti8-through-clickrustusize) | `import click::rust::u32;`; named by path in Rust core-method contracts | specification |
| [`click::rust::option`](#clickrustoption) | `import click::rust::option;` | specification |
| [`click::rust::result`](#clickrustresult) | `import click::rust::result;` | specification |
| [`click::rust::vec`](#clickrustvec) | `import click::rust::vec;` | specification, with trusted axioms |
| [`click::rust::slice`](#clickrustslice) | `import click::rust::slice;` | specification |
| [Rust core interfaces](#rust-core-interfaces), `library/rust/core.interface.click` (not a module) | when a Rust import calls one of its methods | Rust library interface |
| [`click::separation`](#clickseparation) | `import click::separation;` | specification |

`click::primitives` and `click::c::builtins` are implicit too; they hold the
verifier primitives. Any module not marked implicit needs its
`import click::...;` line; see
[Click library imports](../../concepts/sidecars.md#click-library-imports).

## Checking this page

Every declaration below is copied exactly from the library and checked by the
documentation gate. The same gate compares declaration names bidirectionally,
so adding, removing, or changing a public symbol requires a matching reference
update.
A C++ or Rust library interface is named by the path it models,
`std::span<T>::size` or `Vec::push`, and the gate checks that the tests its
**Verified use** cites call it.

A proof inside the library sees only the library theorems declared above
it, in module order. Built-in tactics apply library theorems by name without
a citation, so declaration order is what keeps library proofs acyclic; a
proof that cites a later theorem of its own module is refused with that
reason. Sidecars apply library theorems as declarations and are not limited
this way.

Pure function calls remain symbolic until explicitly unfolded. Predicates
remain opaque until a proof explicitly unfolds them or applies a theorem that
exposes the needed consequence. Theorems can be applied when their stated
requirements are available.

## `click::nat`

Source: `library/nat.click`, implicit.

### Natural numbers

`Nat` is an ordinary recursive logical datatype: `Zero` and `Succ(Nat)`.
Its values are mathematical naturals, with no machine-width bound or wrapping.
Unknown naturals remain symbolic; they are not eagerly built as successor chains.
Addition is a pure recursive definition with checked induction proofs, not a new
kernel arithmetic primitive. Checked `to_integer` and `to_nat` conversions are
available; this slice does not add numeral sugar or implicit conversions to C
integers.

### `Nat`

```click
spec enum Nat {
    Zero,
    Succ(Nat),
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

`to_integer(n)` observes a `Nat` as an exact Integer. `to_nat(z)` requires
`z >= 0` and remains symbolic even for large values. These conversions have
checked builtin meanings, and the laws below relate the two domains without
coercions.

### `nat::to_integer_zero`

```click
theorem to_integer_zero() {
    ensures to_integer(Nat::Zero) == 0;
}
```

### `nat::to_integer_succ`

```click
theorem to_integer_succ(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1;
}
```

### `nat::to_integer_nonnegative`

```click
theorem to_integer_nonnegative(n: Nat) {
    ensures to_integer(n) >= 0;
}
```

### `nat::to_nat_to_integer`

```click
theorem to_nat_to_integer(n: Nat) {
    ensures to_nat(to_integer(n)) == n;
}
```

### `nat::to_integer_to_nat`

```click
theorem to_integer_to_nat(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z;
}
```

### `nat::to_nat_zero`

```click
theorem to_nat_zero() {
    ensures to_nat(0) == Nat::Zero;
}
```

### `nat::add`

```click
function add(left: Nat, right: Nat) -> Nat
    decreases left
{
    match left {
        Nat::Zero => right,
        Nat::Succ(previous) => Nat::Succ(nat::add(previous, right)),
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_left_identity`

```click
theorem add_left_identity(n: Nat) {
    ensures nat::add(Nat::Zero, n) == n by {
        unfold(nat::add(Nat::Zero, n));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_succ_left`

```click
theorem add_succ_left(n: Nat, m: Nat) {
    ensures nat::add(Nat::Succ(n), m) == Nat::Succ(nat::add(n, m)) by {
        unfold(nat::add(Nat::Succ(n), m));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::to_integer_add`

The ordinary structural addition agrees with exact Integer addition. Its proof
uses Nat induction and explicit, locally checked linear certificates.

```click
theorem to_integer_add(n: Nat, m: Nat) {
    ensures to_integer(nat::add(n, m)) == to_integer(n) + to_integer(m) by {
        let ih = induct(n);
        match n {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, m));
                apply(nat::to_integer_zero());
                rewrite(to_integer(Nat::Zero), 0);
                close();
            }
            Nat::Succ(previous) => {
                unfold(nat::add(Nat::Succ(previous), m));
                apply(nat::to_integer_succ(nat::add(previous, m)));
                apply(ih(previous));
                apply(nat::to_integer_succ(previous));
                rewrite(to_integer(Nat::Succ(nat::add(previous, m))), to_integer(nat::add(previous, m)) + 1);
                rewrite(to_integer(nat::add(previous, m)), to_integer(previous) + to_integer(m));
                rewrite(to_integer(Nat::Succ(previous)), to_integer(previous) + 1);
                close();
            }
        }
    }
}
```

### `nat::add_right_identity`

```click
theorem add_right_identity(n: Nat) {
    ensures nat::add(n, Nat::Zero) == n by {
        let ih = induct(n);
        match n {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, Nat::Zero));
                close();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), Nat::Zero));
                rewrite(nat::add(previous, Nat::Zero), previous);
                close();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_succ_right`

```click
theorem add_succ_right(n: Nat, m: Nat) {
    ensures nat::add(n, Nat::Succ(m)) == Nat::Succ(nat::add(n, m)) by {
        let ih = induct(n);
        match n {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, Nat::Succ(m)));
                unfold(nat::add(Nat::Zero, m));
                close();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), Nat::Succ(m)));
                unfold(nat::add(Nat::Succ(previous), m));
                rewrite(nat::add(previous, Nat::Succ(m)), Nat::Succ(nat::add(previous, m)));
                close();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_associative`

```click
theorem add_associative(a: Nat, b: Nat, c: Nat) {
    ensures nat::add(nat::add(a, b), c) == nat::add(a, nat::add(b, c)) by {
        let ih = induct(a);
        match a {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, b));
                unfold(nat::add(Nat::Zero, nat::add(b, c)));
                close();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                apply(nat::add_succ_left(previous, b));
                rewrite(nat::add(Nat::Succ(previous), b), Nat::Succ(nat::add(previous, b)));
                apply(nat::add_succ_left(nat::add(previous, b), c));
                rewrite(nat::add(Nat::Succ(nat::add(previous, b)), c), Nat::Succ(nat::add(nat::add(previous, b), c)));
                apply(nat::add_succ_left(previous, nat::add(b, c)));
                rewrite(nat::add(Nat::Succ(previous), nat::add(b, c)), Nat::Succ(nat::add(previous, nat::add(b, c))));
                rewrite(nat::add(nat::add(previous, b), c), nat::add(previous, nat::add(b, c)));
                close();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_commutative`

```click
theorem add_commutative(a: Nat, b: Nat) {
    ensures nat::add(a, b) == nat::add(b, a) by {
        let ih = induct(a);
        match a {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, b));
                apply(nat::add_right_identity(b));
                rewrite(nat::add(b, Nat::Zero), b);
                close();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), b));
                apply(nat::add_succ_right(b, previous));
                rewrite(nat::add(b, Nat::Succ(previous)), Nat::Succ(nat::add(b, previous)));
                rewrite(nat::add(previous, b), nat::add(b, previous));
                close();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

## `click::list`

Source: `library/list.click`, implicit. `List` and its constructors keep bare names; functions and theorems are written `list::name`.

### Lists

`List<T>` is an immutable logical value, not a C layout or ownership resource.
It preserves order and multiplicity. Use explicit constructors and the functions
below; `[]`, `++`, and `in` still use the older sequence representation.

### `List`

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append`

```click
function append<T>(xs: List<T>, ys: List<T>) -> List<T>
    decreases xs
{
    match xs {
        List::Nil => ys,
        List::Cons(head, tail) => List<T>::Cons(head, list::append(tail, ys)),
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains`

```click
function contains<T>(xs: List<T>, value: T) -> Bool
    decreases xs
{
    match xs {
        List::Nil => false,
        List::Cons(head, tail) =>
            if head == value { true } else { list::contains(tail, value) },
    }
}
```

Returns `true` for membership and `false` otherwise, using element
equality. A call written alone is a claim: `ensures list::contains(xs, v);`
means `list::contains(xs, v) == true`.
Its checked laws support C scalar, pointer, and algebraic-valued elements,
including nested lists. Comparisons of unknown algebraic values stay symbolic.

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_left_identity`

```click
theorem append_left_identity<T>(xs: List<T>) {
    ensures list::append(List<T>::Nil, xs) == xs by {
        unfold(list::append(List<T>::Nil, xs));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_right_identity`

```click
theorem append_right_identity<T>(xs: List<T>) {
    ensures list::append(xs, List<T>::Nil) == xs by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(list::append(List<T>::Nil, List<T>::Nil));
                close();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                unfold(list::append(List<T>::Cons(head, tail), List<T>::Nil));
                rewrite(list::append(tail, List<T>::Nil), tail);
                close();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_cons`

```click
theorem append_cons<T>(head: T, tail: List<T>, ys: List<T>) {
    ensures list::append(List<T>::Cons(head, tail), ys)
        == List<T>::Cons(head, list::append(tail, ys)) by {
        unfold(list::append(List<T>::Cons(head, tail), ys));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_associative`

```click
theorem append_associative<T>(xs: List<T>, ys: List<T>, zs: List<T>) {
    ensures list::append(list::append(xs, ys), zs)
        == list::append(xs, list::append(ys, zs)) by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::append(List<T>::Nil, list::append(ys, zs)));
                close();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                apply(list::append_cons(head, list::append(tail, ys), zs));
                rewrite(list::append(List<T>::Cons(head, list::append(tail, ys)), zs), List<T>::Cons(head, list::append(list::append(tail, ys), zs)));
                apply(list::append_cons(head, tail, list::append(ys, zs)));
                rewrite(list::append(List<T>::Cons(head, tail), list::append(ys, zs)), List<T>::Cons(head, list::append(tail, list::append(ys, zs))));
                rewrite(list::append(list::append(tail, ys), zs), list::append(tail, list::append(ys, zs)));
                close();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains_nil`

```click
theorem contains_nil<T>(value: T) {
    ensures list::contains(List<T>::Nil, value) == false by {
        unfold(list::contains(List<T>::Nil, value));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains_cons`

```click
theorem contains_cons<T>(head: T, tail: List<T>, value: T) {
    ensures list::contains(List<T>::Cons(head, tail), value)
        == if head == value { true } else { list::contains(tail, value) } by {
        unfold(list::contains(List<T>::Cons(head, tail), value));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains_append`

```click
theorem contains_append<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::contains(List<T>::Nil, value));
                close();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                if head == value {
                    apply(list::contains_cons(head, list::append(tail, ys), value));
                    rewrite(list::contains(List<T>::Cons(head, list::append(tail, ys)), value), if head == value { true } else { list::contains(list::append(tail, ys), value) });
                    apply(list::contains_cons(head, tail, value));
                    rewrite(list::contains(List<T>::Cons(head, tail), value), if head == value { true } else { list::contains(tail, value) });
                    have (if head == value { true } else { list::contains(list::append(tail, ys), value) }) == true by close();
                    have (if head == value { true } else { list::contains(tail, value) }) == true by close();
                    have (if (if head == value { true } else { list::contains(tail, value) }) { true } else { list::contains(ys, value) }) == true by {
                        rewrite((if head == value { true } else { list::contains(tail, value) }), true);
                        close();
                    }
                    rewrite((if (if head == value { true } else { list::contains(tail, value) }) { true } else { list::contains(ys, value) }), true);
                    close();
                } else {
                    apply(list::contains_cons(head, list::append(tail, ys), value));
                    rewrite(list::contains(List<T>::Cons(head, list::append(tail, ys)), value), if head == value { true } else { list::contains(list::append(tail, ys), value) });
                    apply(list::contains_cons(head, tail, value));
                    rewrite(list::contains(List<T>::Cons(head, tail), value), if head == value { true } else { list::contains(tail, value) });
                    rewrite(list::contains(list::append(tail, ys), value), if list::contains(tail, value) { true } else { list::contains(ys, value) });
                    have (if head == value { true } else { list::contains(tail, value) }) == list::contains(tail, value) by close();
                    rewrite((if head == value { true } else { list::contains(tail, value) }), list::contains(tail, value));
                    close();
                }
            }
        }
    }
}
```

Membership through append, proved by structural induction with explicit
conditional reduction in each constructor case.

**Verified use:** [`mdtests/stdlib_list_compositionality.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_compositionality.md).

### Natural-valued lengths

`list::length` returns `Nat`, so a length cannot be negative or overflow.
These laws hold for arbitrary element types, including nested lists.

### `list::length`

```click
function length<T>(xs: List<T>) -> Nat
    decreases xs
{
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(head, tail) => Nat::Succ(list::length(tail)),
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list::length_nil`

```click
theorem length_nil<T>(xs: List<T>) {
    requires xs == List<T>::Nil;
    ensures list::length(xs) == Nat::Zero by {
        rewrite(xs, List<T>::Nil);
        unfold(list::length(List<T>::Nil));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list::length_cons`

```click
theorem length_cons<T>(head: T, tail: List<T>) {
    ensures list::length(List<T>::Cons(head, tail)) == Nat::Succ(list::length(tail)) by {
        unfold(list::length(List<T>::Cons(head, tail)));
        close();
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list::length_append`

```click
theorem length_append<T>(xs: List<T>, ys: List<T>) {
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::length(List<T>::Nil));
                unfold(nat::add(Nat::Zero, list::length(ys)));
                close();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                apply(list::length_cons(head, list::append(tail, ys)));
                rewrite(list::length(List<T>::Cons(head, list::append(tail, ys))), Nat::Succ(list::length(list::append(tail, ys))));
                apply(list::length_cons(head, tail));
                rewrite(list::length(List<T>::Cons(head, tail)), Nat::Succ(list::length(tail)));
                apply(nat::add_succ_left(list::length(tail), list::length(ys)));
                rewrite(nat::add(Nat::Succ(list::length(tail)), list::length(ys)), Nat::Succ(nat::add(list::length(tail), list::length(ys))));
                rewrite(list::length(list::append(tail, ys)), nat::add(list::length(tail), list::length(ys)));
                close();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

## `click::option`

Source: `library/option.click`, implicit.

### `Option`

```click
spec enum Option<T> {
    None,
    Some(T),
}
```

**Meaning:** An optional value. A Rust `Option<u32>` parameter or result is
this value in a contract: `ensures result == Option<u32>::Some(x);`. The
importer lays the Rust value out itself; a contract never reads that layout.

## `click::result`

Source: `library/result.click`, implicit.

### `Result`

```click
spec enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

**Meaning:** A value or an error. A Rust `Result<u32, u8>` parameter or result
is this value in a contract: `ensures result == Result<u32, u8>::Ok(x);`. As
for `Option`, the importer lays the Rust value out itself.

## `click::integer`

Source: `library/integer.click`, `import click::integer;`. Width-specific order, definedness and `to_integer` lemmas, unsigned wrapping operations, round trips through the `to_*` conversions, and `Integer` truncating-division laws. [Trust](../../concepts/trust.md#the-click-library) says which theorems are kernel standard theorems.

### Foundational integer order axioms

These trusted laws expose addition of inequalities, nonnegative scaling, and
integer rounding to ordinary `apply(...)` proofs. They state
mathematical Integer laws; machine operations still need their definedness and
observation bridges. The scaling law is
[`integer::multiply_order_nonnegative`](#integermultiply_order_nonnegative).

### `integer::add_le`

```click
axiom add_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c <= d;
    ensures a + c <= b + d;
}
```

**Meaning:** Adds two inequalities. Both input bounds must be explicitly available.

**Kind:** trusted axiom.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::le_antisymmetric`

```click
axiom le_antisymmetric(a: Integer, b: Integer) {
    requires a <= b;
    requires b <= a;
    ensures a == b;
}
```

**Meaning:** Opposite non-strict Integer bounds imply equality.

**Kind:** trusted axiom.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::lt_step_le`

```click
axiom lt_step_le(a: Integer, b: Integer) {
    requires a < b;
    ensures a + 1 <= b;
}
```

**Kind:** axiom. Integer discreteness turns a strict bound into its successor bound.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::step_le_lt`

```click
theorem step_le_lt(a: Integer, b: Integer) {
    requires a + 1 <= b;
    ensures a < b by {
        if a < b {
            close();
        } else {
            have b <= a by { close(); }
            have a + 1 + b <= b + a by {
                apply(integer::add_le(a + 1, b, b, a));
            }
            contradiction(a + 1 + b <= b + a);
        }
    }
}
```

**Kind:** proved theorem. The successor bound implies strict order.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::le_ne_lt`

```click
theorem le_ne_lt(a: Integer, b: Integer) {
    requires a <= b;
    requires a != b;
    ensures a < b by {
        if a < b {
            close();
        } else {
            have b <= a by { close(); }
            have a == b by {
                apply(integer::le_antisymmetric(a, b));
            }
            contradiction(a == b);
        }
    }
}
```

**Kind:** proved theorem. A non-strict bound and disequality imply strict order.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::le_substitute`

```click
theorem le_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c == a;
    requires d == b;
    ensures c <= d by { rewrite(c, a); rewrite(d, b); close(); }
}
```

**Kind:** proved theorem. These congruence and substitution laws keep affine
composition explicit, including applications whose concrete equality guards
evaluate to `true`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::equal_substitute`

```click
theorem equal_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == a;
    requires d == b;
    ensures c == d by { rewrite(c, a); rewrite(d, b); close(); }
}
```

**Kind:** proved theorem. These congruence and substitution laws keep affine
composition explicit, including applications whose concrete equality guards
evaluate to `true`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::le_difference`

```click
theorem le_difference(a:Integer,b:Integer,value:Integer) {
 requires a<=b;
 requires value==a-b;
 ensures value<=0 by {
  have a + -b <= b + -b by {
   apply(click::integer::add_le(a,b,-b,-b));
  }
  have value == a + -b by { rewrite(value,a-b); close(); }
  have 0 == b + -b by close();
  apply(click::integer::le_substitute(a + -b,b + -b,value,0));
 }
}
```

**Kind:** proved theorem.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::difference_le`

```click
theorem difference_le(a:Integer,b:Integer,value:Integer) {
 requires value<=0;
 requires value==a-b;
 ensures a<=b by {
  have value + b <= 0 + b by {
   apply(click::integer::add_le(value,0,b,b));
  }
  have a == value + b by { rewrite(value,a-b); close(); }
  have b == 0 + b by close();
  apply(click::integer::le_substitute(value+b,0+b,a,b));
 }
}
```

**Kind:** proved theorem.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::equal_difference`

```click
theorem equal_difference(a: Integer, b: Integer) {
    requires a == b;
    ensures a - b == 0 by { rewrite(a, b); close(); }
}
```

**Kind:** proved theorem. These congruence and substitution laws keep affine
composition explicit, including applications whose concrete equality guards
evaluate to `true`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::equal_add`

```click
theorem equal_add(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == d;
    ensures a + c == b + d by { rewrite(a, b); rewrite(c, d); close(); }
}
```

**Kind:** proved theorem. These congruence and substitution laws keep affine
composition explicit, including applications whose concrete equality guards
evaluate to `true`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::equal_multiply`

```click
theorem equal_multiply(a: Integer, b: Integer, factor: Integer) {
    requires a == b;
    ensures a * factor == b * factor by { rewrite(a, b); close(); }
}
```

**Kind:** proved theorem. These congruence and substitution laws keep affine
composition explicit, including applications whose concrete equality guards
evaluate to `true`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::equal_le`

```click
theorem equal_le(a: Integer, b: Integer) {
    requires a == b;
    ensures a <= b by { rewrite(a, b); close(); }
}
```

**Kind:** proved theorem. These congruence and substitution laws keep affine
composition explicit, including applications whose concrete equality guards
evaluate to `true`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::round_down_le`

```click
axiom round_down_le(value: Integer, bound: Integer, divisor: Integer, remainder: Integer) {
    requires 0 < divisor;
    requires remainder < divisor;
    requires value * divisor <= bound * divisor + remainder;
    ensures value <= bound;
}
```

**Meaning:** Rounds an upper bound down to an integer. A positive divisor and a remainder strictly below it are required; the remainder may be negative.

**Kind:** trusted axiom.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### Order, definedness and conversion lemmas

### `integer::int32_add_defined_by_integer_bounds`

```click
theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        close();
    }
}
```

Bounds on the mathematical sum establish that signed C addition does not overflow.
Both bounds are required, including when the final program result is in range.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_add_to_integer`

```click
theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 + 0 <= (to_integer(left) + to_integer(right)) by {
            apply(integer::add_le(0, to_integer(left), 0, to_integer(right)));
        }
        have 0 <= (to_integer(left) + to_integer(right)) by close();
        close();
    }
}
```

Unsigned machine addition agrees with mathematical addition when the mathematical sum fits `uint32`. Unsigned definedness alone allows wrapping and cannot establish this equality.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_subtract_to_integer`

```click
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have to_integer(right) <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have to_integer(left) <= 4294967295 by close();
        have to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)) by {
            apply(integer::add_le(to_integer(right), to_integer(left), -to_integer(right), -to_integer(right)));
        }
        have 0 == to_integer(right) + -to_integer(right) by close();
        have (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)) by close();
        have 0 <= (to_integer(left) - to_integer(right)) by {
            apply(integer::le_substitute(to_integer(right) + -to_integer(right), (to_integer(left) + -to_integer(right)), 0, (to_integer(left) - to_integer(right))));
        }
        have -to_integer(right) <= 0 by {
            apply(integer::negate_order(0, to_integer(right)));
            close();
        }
        have (to_integer(left) + -to_integer(right)) <= 4294967295 + 0 by {
            apply(integer::add_le(to_integer(left), 4294967295, -to_integer(right), 0));
        }
        have to_integer(4294967295u64) == 4294967295 + 0 by close();
        have (to_integer(left) - to_integer(right)) <= 4294967295 by {
            apply(integer::le_substitute((to_integer(left) + -to_integer(right)), 4294967295 + 0, (to_integer(left) - to_integer(right)), 4294967295));
        }
        close();
    }
}
```

Unsigned subtraction agrees with Integer subtraction under the native unsigned no-underflow guard. The rule covers the full `uint32` range. Native definedness alone permits wrapping, so it cannot replace the guard.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_divide_to_integer`

```click
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}
```

Unsigned division agrees with Integer truncating division when both evaluation domains exclude zero. No overflow bound on the dividend is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_remainder_to_integer`

```click
theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Unsigned remainder agrees with Integer truncating remainder when both evaluation domains exclude zero. A machine comparison is read through its `to_integer` observations, so the native guard `right != 0u32` alone meets both premises.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_multiply_to_integer`

```click
theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 * to_integer(right) <= (to_integer(left) * to_integer(right)) by {
            apply(integer::multiply_order_nonnegative(0, to_integer(left), to_integer(right)));
        }
        have 0 <= (to_integer(left) * to_integer(right)) by close();
        if right == 0u32 {
            have to_integer(right) == 0 by close();
            have (to_integer(left) * to_integer(right)) == 0 by {
                rewrite(to_integer(right), 0);
                close();
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_substitute(0, 4294967295, (to_integer(left) * to_integer(right)), 4294967295));
            }
            close();
        } else {
            have to_integer(right) != 0 by close();
            have to_integer(left) <= to_integer(4294967295u32 / right) by {
                cases {
                    right == 0u32 => { contradiction(right == 0u32); }
                    to_integer(left) <= to_integer(4294967295u32 / right) => { close(); }
                }
            }
            have to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right)) by {
                apply(integer::uint32_divide_to_integer(4294967295u32, right));
            }
            have to_integer(left) <= truncating_quotient(4294967295, to_integer(right)) by {
                rewrite(truncating_quotient(4294967295, to_integer(right)), to_integer(4294967295u32 / right));
                close();
            }
            have 4294967295 == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::truncation_identity(4294967295, to_integer(right)));
            }
            have 0 <= truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::nonnegative_dividend_remainder(4294967295, to_integer(right)));
            }
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0 <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::add_le((truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 0, truncating_remainder(4294967295, to_integer(right))));
            }
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0 by close();
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_substitute((truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0, (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 4294967295));
            }
            have (to_integer(left) * to_integer(right)) <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) by {
                apply(integer::multiply_order_nonnegative(to_integer(left), truncating_quotient(4294967295, to_integer(right)), to_integer(right)));
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_transitive((to_integer(left) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 4294967295));
            }
            close();
        }
    }
}
```

Unsigned multiplication agrees with Integer multiplication under the native no-overflow guard. A zero right operand satisfies the guard without division; other operands must fit the unsigned quotient ceiling. Native unsigned definedness alone permits wrapping.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_multiply_guard_by_integer_bound`

```click
theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        if right != 0u32 {
            have to_integer(right) != 0 by close();
            have 0 <= to_integer(right) by close();
            have 0 < to_integer(right) by {
                apply(integer::le_ne_lt(0, to_integer(right)));
            }
            apply(integer::lt_step_le(0, to_integer(right)));
            have 1 <= to_integer(right) by close();
            apply(integer::positive_divisor_quotient_lower(4294967295, to_integer(right), to_integer(left)));
            apply(integer::uint32_divide_to_integer(4294967295u32, right));
            have to_integer(left) <= to_integer(4294967295u32 / right) by {
                rewrite(to_integer(4294967295u32 / right), truncating_quotient(4294967295, to_integer(right)));
                close();
            }
            have left <= 4294967295u32 / right by close();
            close();
        } else {
            have right == 0u32 by close();
            close();
        }
    }
}
```

A mathematical product bound establishes the native checked-multiplication guard used by Rust. The zero right operand needs no division. Combine this rule with `integer::uint32_multiply_to_integer` to prove an exact product from Integer bounds; bounding the already wrapped machine product is insufficient.

**Verified use:** [`mdtests/integer_uint32_product_bound_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_uint32_product_bound_guard.md).

### `integer::uint64_add_to_integer`

```click
theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 + 0 <= (to_integer(left) + to_integer(right)) by {
            apply(integer::add_le(0, to_integer(left), 0, to_integer(right)));
        }
        have 0 <= (to_integer(left) + to_integer(right)) by close();
        close();
    }
}
```

Unsigned addition agrees with Integer addition when the sum fits uint64. Native unsigned definedness alone permits wrapping.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_increment_lower_bound`

```click
theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 2147483647 by close();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 2147483647));
        }
        have defined(value + 1) by close();
        apply(integer::int32_add_to_integer(value, 1));
        apply(integer::le_transitive(to_integer(lower), to_integer(value), to_integer(value) + 1));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(lower) <= to_integer(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_increment_upper_bound`

```click
theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 2147483647 by close();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 2147483647));
        }
        have defined(value + 1) by close();
        apply(integer::int32_add_to_integer(value, 1));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value + 1) <= to_integer(upper)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_increment_strictly_increases`

```click
theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 2147483647 by close();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 2147483647));
        }
        have defined(value + 1) by close();
        apply(integer::int32_add_to_integer(value, 1));
        have to_integer(value) < to_integer(value) + 1 by close();
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value) < to_integer(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_increment_below_max_is_defined`

```click
theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::lt_step_le(to_integer(value), 2147483647));
        }
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `defined(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_increment_upper_bound`

```click
theorem uint64_increment_upper_bound(value: uint64, upper: uint64) {
    requires value < upper;
    ensures to_integer(value + 1u64) <= to_integer(upper) by {
        have to_integer(value) < to_integer(upper) by close();
        have (to_integer(value) + 1) <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 18446744073709551615 by close();
        have (to_integer(value) + 1) <= 18446744073709551615 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 18446744073709551615));
        }
        have (to_integer(value) + to_integer(1u64)) <= 18446744073709551615 by close();
        have to_integer(value + 1u64) == (to_integer(value) + 1) by {
            apply(integer::uint64_add_to_integer(value, 1u64));
            close();
        }
        rewrite(to_integer(value + 1u64), to_integer(value) + 1);
        close();
    }
}
```

The strict bound on the original value proves the increment fits in `uint64`
and the incremented word remains at most the upper bound.

**Verified use:** [`mdtests/back_edge_closes_an_unsigned_bound_from_the_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/back_edge_closes_an_unsigned_bound_from_the_guard.md).

### `integer::uint64_multiply_to_integer`

```click
theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 * to_integer(right) <= (to_integer(left) * to_integer(right)) by {
            apply(integer::multiply_order_nonnegative(0, to_integer(left), to_integer(right)));
        }
        have 0 <= (to_integer(left) * to_integer(right)) by close();
        close();
    }
}
```

Unsigned multiplication agrees with the Integer product when it fits uint64. The explicit product bound excludes wrap.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_product_bound_from_division`

```click
theorem uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by {
        have to_integer(y) != 0;
        have 0 <= to_integer(y);
        have 0 <= to_integer(18446744073709551615u64) by close();
        apply(integer::uint64_divide_to_integer(18446744073709551615u64, y));
        have to_integer(x) <= to_integer(18446744073709551615u64 / y);
        apply(integer::multiply_order_nonnegative(to_integer(x), to_integer(18446744073709551615u64 / y), to_integer(y)));
        apply(integer::truncation_identity(to_integer(18446744073709551615u64), to_integer(y)));
        apply(integer::nonnegative_dividend_remainder(to_integer(18446744073709551615u64), to_integer(y)));
        have to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) by {
            rewrite(to_integer(18446744073709551615u64 / y), truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)));
            close();
        }
        close() using {
            to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64 / y) * to_integer(y);
            to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y);
            to_integer(18446744073709551615u64) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) + truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
            0 <= truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
        };
    }
}
```

A nonzero native divisor and `x <= 18446744073709551615u64 / y` bound the
exact Integer product. Use this before `integer::uint64_multiply_to_integer` when the
program exposes a division-based overflow guard.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_subtract_to_integer`

```click
theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have to_integer(right) <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have to_integer(left) <= 18446744073709551615 by close();
        have to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)) by {
            apply(integer::add_le(to_integer(right), to_integer(left), -to_integer(right), -to_integer(right)));
        }
        have 0 == to_integer(right) + -to_integer(right) by close();
        have (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)) by close();
        have 0 <= (to_integer(left) - to_integer(right)) by {
            apply(integer::le_substitute(to_integer(right) + -to_integer(right), (to_integer(left) + -to_integer(right)), 0, (to_integer(left) - to_integer(right))));
        }
        have -to_integer(right) <= 0 by {
            apply(integer::negate_order(0, to_integer(right)));
            close();
        }
        have (to_integer(left) + -to_integer(right)) <= 18446744073709551615 + 0 by {
            apply(integer::add_le(to_integer(left), 18446744073709551615, -to_integer(right), 0));
        }
        have to_integer(18446744073709551615u64) == 18446744073709551615 + 0 by close();
        have (to_integer(left) - to_integer(right)) <= 18446744073709551615 by {
            apply(integer::le_substitute((to_integer(left) + -to_integer(right)), 18446744073709551615 + 0, (to_integer(left) - to_integer(right)), 18446744073709551615));
        }
        close();
    }
}
```

Unsigned subtraction agrees with Integer subtraction when the subtrahend is at most the minuend, excluding underflow.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_divide_to_integer`

```click
theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}
```

Unsigned division agrees with the truncating Integer quotient. Both native and observed nonzero divisor premises are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_remainder_to_integer`

```click
theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Unsigned remainder agrees with the truncating Integer remainder. Both native and observed nonzero divisor premises are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_to_integer_less_equal_implies_less_equal`

```click
theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}
```

Exact Integer observation order implies native uint64 non-strict order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_pack_uint16_to_integer`

```click
theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value when both native bounds hold.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_pack_uint16_high_first_to_integer`

```click
theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value with the shifted high field written first. Both native bounds are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_unpack_uint16_low`

```click
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_unpack_uint16_high`

```click
theorem uint32_unpack_uint16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

These exact word identities require both fields to fit in 16 bits. The high
word uses a logical right shift, so the identity also holds when the packed
word's top bit is set. Their bounds are checked premises of the kernel rules.

### `integer::uint64_pack_uint16_to_integer`

```click
theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value when both native bounds hold.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_unpack_uint16_low`

```click
theorem uint64_unpack_uint16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_unpack_uint16_high`

```click
theorem uint64_unpack_uint16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

The kernel issues these exact LP64 word identities only with both 16-bit field
bounds. They retain all packed bits, including bit 31; the high field uses a
logical right shift.

### `integer::uint64_less_than_implies_not_greater_equal`

```click
theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by close();
}
```

A strict unsigned order excludes the opposite greater-or-equal branch.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_less_equal_to_integer`

```click
theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by close();
}
```

Preserves native unsigned order in exact Integer observations, including values above the sign bit. The native order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_to_integer_less_equal_implies_less_equal`

```click
theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}
```

Reflects exact Integer observation order into native unsigned order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_to_integer_equal_implies_equal`

```click
theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by close();
}
```

Reflects equal exact Integer observations into native unsigned equality. Every
32-bit pattern, including those above the signed sign bit, has one unsigned
Integer value, so the observation is injective.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_remainder_less_than_divisor`

```click
theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by {
        have to_integer(divisor) != 0 by close();
        have 0 <= to_integer(divisor) by close();
        have 0 < to_integer(divisor) by {
            apply(integer::le_ne_lt(0, to_integer(divisor)));
        }
        apply(integer::uint32_remainder_to_integer(value, divisor));
        apply(integer::positive_divisor_remainder_upper(to_integer(value), to_integer(divisor)));
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= (to_integer(divisor) - 1) + 1 by {
            apply(integer::add_le(truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(divisor) - 1, 1, 1));
        }
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= to_integer(divisor) by {
            have to_integer(divisor) == (to_integer(divisor) - 1) + 1 by close();
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, (to_integer(divisor) - 1) + 1, truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor)));
        }
        have to_integer(value % divisor) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1 by {
            apply(integer::equal_add(to_integer(value % divisor), truncating_remainder(to_integer(value), to_integer(divisor)), 1, 1));
        }
        have to_integer(value % divisor) + 1 <= to_integer(divisor) by {
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor), to_integer(value % divisor) + 1, to_integer(divisor)));
        }
        apply(integer::step_le_lt(to_integer(value % divisor), to_integer(divisor)));
    }
}
```

The unsigned remainder is below its divisor for any dividend. The nonzero divisor premise is essential.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_to_integer_bounds`

```click
theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(integer::uint32_less_equal_to_integer(0u32, value));
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(integer::uint32_less_equal_to_integer(value, 4294967295u32));
    }
}
```

Proves the full unsigned observation range from native order. This theorem does not distribute observations over wrapping operations.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_add_to_integer`

```click
theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have -2147483648 <= to_integer(left) + to_integer(right) by {
            close();
        }
        have to_integer(left) + to_integer(right) <= 2147483647 by {
            close();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            close();
        }
        close();
    }
}
```

A defined signed C addition has the same value as mathematical Integer addition.
The definedness premise excludes overflow; the equality is not unconditional.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int64_subtract_to_integer`

```click
theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -9223372036854775808 <= to_integer(left) - to_integer(right) by {
            close();
        }
        have to_integer(left) - to_integer(right) <= 9223372036854775807 by {
            close();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            close();
        }
        close();
    }
}
```

A defined signed 64-bit operation has its exact mathematical Integer value.
The native definedness premise excludes overflow; this law does not establish
that premise or infer any operand range.

**Verified use:** [`mdtests/int64_integer_operation_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/int64_integer_operation_bridges.md).

### `integer::int32_subtract_to_integer`

```click
theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -2147483648 <= to_integer(left) - to_integer(right) by {
            close();
        }
        have to_integer(left) - to_integer(right) <= 2147483647 by {
            close();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            close();
        }
        close();
    }
}
```

A defined signed C subtraction has the same value as mathematical Integer subtraction.
The definedness premise excludes overflow; the equality is not unconditional.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_less_equal_to_integer`

```click
theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by close();
}
```

A signed C order fact transfers to the exact mathematical observations of the
two operands. The C order premise is required; the bridge does not assume an
order between unrelated machine values.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_to_integer_less_equal_implies_less_equal`

```click
theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}
```

A proved non-strict order between exact signed observations establishes the native order. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `integer::int64_to_integer_less_equal_implies_less_equal`

```click
theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}
```

A proved non-strict order between exact signed observations establishes the native order. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `integer::uint32_difference_decreases_after_increment`

```click
axiom uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;
    ensures to_integer((0u32 - value) + (bound - 1u32)) < to_integer((0u32 - value) + bound);
}
```

**Axiom:** trusted, not proved. Under `value < bound` neither `bound - value` nor `(bound - 1) - value` wraps, so the left side is one less than the right.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_less_equal_and_not_less_than_implies_equal`

```click
theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        have to_integer(right) <= to_integer(left) by close();
        apply(integer::le_antisymmetric(to_integer(left), to_integer(right)));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `left == right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_less_equal_and_not_equal_implies_less_than`

```click
theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        have to_integer(left) != to_integer(right) by close();
        apply(integer::le_ne_lt(to_integer(left), to_integer(right)));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `left < right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### Unsigned wrapping arithmetic

`import click::integer;` provides the C operations on unsigned
values, which wrap modulo `2^32` or `2^64`, as functions. A
specification's `+`, `-` and `*` compare exact
Integers, so a claim about C's modular result names these instead; a
comparison between machine values with no Integer arithmetic keeps its C
meaning (`mdtests/wrapping_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.md`).

### `integer::uint32_wrapping_add`

```click
function uint32_wrapping_add(left: uint32, right: uint32) -> uint32 {
    left + right
}
```

**Meaning:** The C uint32 sum `left + right`, reduced modulo 2^32.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_wrapping_sub`

```click
function uint32_wrapping_sub(left: uint32, right: uint32) -> uint32 {
    left - right
}
```

**Meaning:** The C uint32 difference `left - right`, reduced modulo 2^32.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_wrapping_mul`

```click
function uint32_wrapping_mul(left: uint32, right: uint32) -> uint32 {
    left * right
}
```

**Meaning:** The C uint32 product `left * right`, reduced modulo 2^32.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_wrapping_add`

```click
function uint64_wrapping_add(left: uint64, right: uint64) -> uint64 {
    left + right
}
```

**Meaning:** The C uint64 sum `left + right`, reduced modulo 2^64.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_wrapping_sub`

```click
function uint64_wrapping_sub(left: uint64, right: uint64) -> uint64 {
    left - right
}
```

**Meaning:** The C uint64 difference `left - right`, reduced modulo 2^64.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_wrapping_mul`

```click
function uint64_wrapping_mul(left: uint64, right: uint64) -> uint64 {
    left * right
}
```

**Meaning:** The C uint64 product `left * right`, reduced modulo 2^64.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### Integer round trips

### `integer::to_int8_round_trip`

```click
theorem to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by {
        have -128 <= z by {
            close();
        }
        have z <= 127 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `int8` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.


### `integer::to_int16_round_trip`

```click
theorem to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by {
        have -32768 <= z by {
            close();
        }
        have z <= 32767 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `int16` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_int32_round_trip`

```click
theorem to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by {
        have -2147483648 <= z by {
            close();
        }
        have z <= 2147483647 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `int32` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint8_round_trip`

```click
theorem to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 255 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `uint8` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint16_round_trip`

```click
theorem to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 65535 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `uint16` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint32_round_trip`

```click
theorem to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 4294967295 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `uint32` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_int64_round_trip`

```click
theorem to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by {
        have -9223372036854775808 <= z by {
            close();
        }
        have z <= 9223372036854775807 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `int64` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint64_round_trip`

```click
theorem to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 18446744073709551615 by {
            close();
        }
        close();
    }
}
```

An Integer within the exact `uint64` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### Mathematical truncating division

These Integer laws use truncation toward zero, independently of native machine
widths and of the planned Euclidean `/` and `%` operators. They do not establish
native division or narrowing safety.

### `integer::truncation_identity`

```click
theorem truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}
```

### `integer::positive_divisor_remainder_lower`

```click
theorem positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}
```

### `integer::positive_divisor_remainder_upper`

```click
theorem positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}
```

### `integer::nonnegative_dividend_remainder`

```click
theorem nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}
```

### `integer::nonpositive_dividend_remainder`

```click
theorem nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}
```


### `integer::multiply_add`

```click
axiom multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c;
}
```


### `integer::floor_from_remainder`

```click
theorem floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value, q + -1);
            rewrite((q + -1) * d, q * d + -1 * d);
            close() using { n == q * d + r; 1 - d <= r; };
        } else {
            have 0 <= r by { close() using { not (r < 0); }; }
            have value == q;
            rewrite(value, q);
            close() using { n == q * d + r; 0 <= r; };
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { close() using { value == q + -1; }; }
            rewrite(value + 1, q);
            close() using { n == q * d + r; r < 0; };
        } else {
            have 0 <= r by { close() using { not (r < 0); }; }
            have value == q;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value, q);
            rewrite((q + 1) * d, q * d + 1 * d);
            close() using { n == q * d + r; r <= d - 1; };
        }
    }
}
```


### `integer::ceiling_from_remainder`

```click
theorem ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value, q + 1);
            rewrite((q + 1) * d, q * d + 1 * d);
            close() using { n == q * d + r; r <= d - 1; };
        } else {
            have r <= 0 by { close() using { not (0 < r); }; }
            have value == q;
            rewrite(value, q);
            close() using { n == q * d + r; r <= 0; };
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { close() using { value == q + 1; }; }
            rewrite(value + -1, q);
            close() using { n == q * d + r; 0 < r; };
        } else {
            have r <= 0 by { close() using { not (0 < r); }; }
            have value == q;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value, q);
            rewrite((q + -1) * d, q * d + -1 * d);
            close() using { n == q * d + r; 1 - d <= r; };
        }
    }
}
```


### `integer::positive_divisor_quotient_lower`

```click
theorem positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires (bound * d) <= n;
    ensures bound <= truncating_quotient(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have truncating_remainder(n, d) <= (d - 1) by {
            apply(integer::positive_divisor_remainder_upper(n, d));
        }
        have -(d - 1) <= -(truncating_remainder(n, d)) by {
            apply(integer::negate_order(truncating_remainder(n, d), (d - 1)));
        }
        have (bound * d) + -(d - 1) <= n + -(truncating_remainder(n, d)) by {
            apply(integer::add_le((bound * d), n, -(d - 1), -(truncating_remainder(n, d))));
        }
        have (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d) by {
            have (bound * d) - (d - 1) == (bound * d) + -(d - 1) by {
                close();
            }
            have (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)) by {
                close();
            }
            apply(integer::le_substitute((bound * d) + -(d - 1), n + -(truncating_remainder(n, d)), (bound * d) - (d - 1), (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)) by {
            apply(integer::negate_order((bound * d) - (d - 1), (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
            apply(integer::negate_multiply(truncating_quotient(n, d), d));
        }
        have -bound * d == -(bound * d) by {
            apply(integer::negate_multiply(bound, d));
        }
        have -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1) by {
            have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
                rewrite(-(truncating_quotient(n, d)) * d, -(truncating_quotient(n, d) * d));
                close();
            }
            have -bound * d + (d - 1) == -((bound * d) - (d - 1)) by {
                rewrite(-bound * d, -(bound * d));
                close();
            }
            apply(integer::le_substitute(-(truncating_quotient(n, d) * d), -((bound * d) - (d - 1)), -(truncating_quotient(n, d)) * d, -bound * d + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        have -(truncating_quotient(n, d)) <= -bound by {
            apply(integer::round_down_le(-(truncating_quotient(n, d)), -bound, d, (d - 1)));
        }
        have -(-bound) <= -(-(truncating_quotient(n, d))) by {
            apply(integer::negate_order(-(truncating_quotient(n, d)), -bound));
        }
        have bound == -(-bound) by {
            close();
        }
        have truncating_quotient(n, d) == -(-(truncating_quotient(n, d))) by {
            close();
        }
        apply(integer::le_substitute(-(-bound), -(-(truncating_quotient(n, d))), bound, truncating_quotient(n, d)));
    }
}
```


### `integer::positive_divisor_quotient_upper`

```click
theorem positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= (bound * d);
    ensures truncating_quotient(n, d) <= bound by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 1 - d <= truncating_remainder(n, d) by {
            apply(integer::positive_divisor_remainder_lower(n, d));
        }
        have -(truncating_remainder(n, d)) <= (d - 1) by {
            have -(truncating_remainder(n, d)) <= -(1 - d) by {
                apply(integer::negate_order(1 - d, truncating_remainder(n, d)));
            }
            have -(truncating_remainder(n, d)) == -(truncating_remainder(n, d)) by {
                close();
            }
            have (d - 1) == -(1 - d) by {
                close();
            }
            apply(integer::le_substitute(-(truncating_remainder(n, d)), -(1 - d), -(truncating_remainder(n, d)), (d - 1)));
        }
        have n + -(truncating_remainder(n, d)) <= (bound * d) + (d - 1) by {
            apply(integer::add_le(n, (bound * d), -(truncating_remainder(n, d)), (d - 1)));
        }
        have (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1) by {
            have (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)) by {
                close();
            }
            have (bound * d) + (d - 1) == (bound * d) + (d - 1) by {
                close();
            }
            apply(integer::le_substitute(n + -(truncating_remainder(n, d)), (bound * d) + (d - 1), (truncating_quotient(n, d) * d), (bound * d) + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        apply(integer::round_down_le(truncating_quotient(n, d), bound, d, (d - 1)));
    }
}
```


### `integer::positive_divisor_quotient_strict_lower`

```click
theorem positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { close() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            close();
        } else {
            have truncating_quotient(n, d) == bound by { close() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { close() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    close();
                }
                have not (bound * d < n) by { close() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { close() using { not (n <= 0); }; }
                have 0 * d <= n by { close() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { close() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                }; }
                contradiction(bound < 0);
            }
        }
    }
}
```

### `integer::positive_divisor_quotient_strict_upper`

```click
theorem positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { close() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            close();
        } else {
            have truncating_quotient(n, d) == bound by { close() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { close() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    close();
                }
                have not (n < bound * d) by { close() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { close() using { not (0 <= n); }; }
                have n <= 0 * d by { close() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { close() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                }; }
                contradiction(0 < bound);
            }
        }
    }
}
```

### `integer::lower_correction_bound`

```click
theorem lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            close();
        } else {
            have q == lower by { close() using { lower <= q; not (lower + 1 <= q); }; }
            have n == lower * d + r by {
                rewrite(lower, q);
                close();
            }
            have not (r < 0) by { close() using { lower * d <= n; n == lower * d + r; }; }
            contradiction(r < 0);
        }
    }
}
```


### `integer::upper_correction_bound`

```click
theorem upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            close();
        } else {
            have q == upper by { close() using { q <= upper; not (q <= upper + -1); }; }
            have n == upper * d + r by {
                rewrite(upper, q);
                close();
            }
            have not (0 < r) by { close() using { n <= upper * d; n == upper * d + r; }; }
            contradiction(0 < r);
        }
    }
}
```

### `integer::multiply_order_nonnegative`

```click
axiom multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor;
}
```

### `integer::multiply_order_nonpositive`

```click
theorem multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        have 0 <= -factor by {
            have factor + -factor <= 0 + -factor by {
                apply(integer::add_le(factor, 0, -factor, -factor));
            }
            have 0 == factor + -factor by { close(); }
            have -factor == 0 + -factor by { close(); }
            rewrite(0, factor + -factor);
            rewrite(-factor, 0 + -factor);
            close();
        }
        have a * -factor <= b * -factor by {
            apply(integer::multiply_order_nonnegative(a, b, -factor));
        }
        have -(b * -factor) <= -(a * -factor) by {
            apply(integer::negate_order(a * -factor, b * -factor));
        }
        have b * -factor == -(b * factor) by { apply(integer::multiply_negate(b, factor)); }
        have a * -factor == -(a * factor) by { apply(integer::multiply_negate(a, factor)); }
        have b * factor == -(-(b * factor)) by { close(); }
        have a * factor == -(-(a * factor)) by { close(); }
        rewrite(b * factor, -(-(b * factor)));
        rewrite(a * factor, -(-(a * factor)));
        rewrite(-(b * factor), b * -factor);
        rewrite(-(a * factor), a * -factor);
        close();
    }
}
```

### `integer::multiply_commutative`

```click
axiom multiply_commutative(a: Integer, b: Integer) {
    ensures a * b == b * a;
}
```

### `integer::multiply_negate`

```click
axiom multiply_negate(a: Integer, b: Integer) {
    ensures a * -b == -(a * b);
}
```

### `integer::negate_order`

```click
theorem negate_order(a: Integer, b: Integer) {
    requires a <= b;
    ensures -b <= -a by {
        have a + (-a + -b) <= b + (-a + -b) by {
            apply(integer::add_le(a, b, -a + -b, -a + -b));
        }
        have -b == a + (-a + -b) by { close(); }
        have -a == b + (-a + -b) by { close(); }
        rewrite(-b, a + (-a + -b));
        rewrite(-a, b + (-a + -b));
        close();
    }
}
```

### `integer::le_transitive`

```click
theorem le_transitive(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    requires b <= c;
    ensures a <= c by {
        have a + b <= b + c by {
            apply(integer::add_le(a, b, b, c));
        }
        have (a + b) + -b <= (b + c) + -b by {
            apply(integer::add_le(a + b, b + c, -b, -b));
        }
        have a == (a + b) + -b by { close(); }
        have c == (b + c) + -b by { close(); }
        rewrite(a, (a + b) + -b);
        rewrite(c, (b + c) + -b);
        close();
    }
}
```

### `integer::product_lower_bound`

```click
theorem product_lower_bound(x: Integer, y: Integer, lo_x: Integer, hi_x: Integer, lo_y: Integer, hi_y: Integer, bound: Integer) {
    requires lo_x <= x;
    requires x <= hi_x;
    requires lo_y <= y;
    requires y <= hi_y;
    requires bound <= lo_x * lo_y;
    requires bound <= lo_x * hi_y;
    requires bound <= hi_x * lo_y;
    requires bound <= hi_x * hi_y;
    ensures bound <= x * y by {
        have x * y == y * x by { apply(integer::multiply_commutative(x, y)); }
        if 0 <= x {
            have lo_y * x <= y * x by {
                apply(integer::multiply_order_nonnegative(lo_y, y, x));
            }
            if 0 <= lo_y {
                have lo_x * lo_y <= x * lo_y by {
                    apply(integer::multiply_order_nonnegative(lo_x, x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have bound <= lo_y * x by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(bound, lo_x * lo_y, x * lo_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, lo_y * x, y * x));
            } else {
                have lo_y < 0 by { close(); }
                have lo_y <= 0 by {
                    apply(integer::lt_le(lo_y, 0));
                }
                have hi_x * lo_y <= x * lo_y by {
                    apply(integer::multiply_order_nonpositive(x, hi_x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have bound <= lo_y * x by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(bound, hi_x * lo_y, x * lo_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, lo_y * x, y * x));
            }
        } else {
            have x < 0 by { close(); }
                have x <= 0 by {
                    apply(integer::lt_le(x, 0));
                }
            have hi_y * x <= y * x by {
                apply(integer::multiply_order_nonpositive(y, hi_y, x));
            }
            if 0 <= hi_y {
                have lo_x * hi_y <= x * hi_y by {
                    apply(integer::multiply_order_nonnegative(lo_x, x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have bound <= hi_y * x by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(bound, lo_x * hi_y, x * hi_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, hi_y * x, y * x));
            } else {
                have hi_y < 0 by { close(); }
                have hi_y <= 0 by {
                    apply(integer::lt_le(hi_y, 0));
                }
                have hi_x * hi_y <= x * hi_y by {
                    apply(integer::multiply_order_nonpositive(x, hi_x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have bound <= hi_y * x by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(bound, hi_x * hi_y, x * hi_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, hi_y * x, y * x));
            }
        }
    }
}
```

### `integer::product_upper_bound`

```click
theorem product_upper_bound(x: Integer, y: Integer, lo_x: Integer, hi_x: Integer, lo_y: Integer, hi_y: Integer, bound: Integer) {
    requires lo_x <= x;
    requires x <= hi_x;
    requires lo_y <= y;
    requires y <= hi_y;
    requires lo_x * lo_y <= bound;
    requires lo_x * hi_y <= bound;
    requires hi_x * lo_y <= bound;
    requires hi_x * hi_y <= bound;
    ensures x * y <= bound by {
        have x * y == y * x by { apply(integer::multiply_commutative(x, y)); }
        if 0 <= x {
            have y * x <= hi_y * x by {
                apply(integer::multiply_order_nonnegative(y, hi_y, x));
            }
            if 0 <= hi_y {
                have x * hi_y <= hi_x * hi_y by {
                    apply(integer::multiply_order_nonnegative(x, hi_x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have hi_y * x <= bound by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(x * hi_y, hi_x * hi_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, hi_y * x, bound));
            } else {
                have hi_y < 0 by { close(); }
                have hi_y <= 0 by {
                    apply(integer::lt_le(hi_y, 0));
                }
                have x * hi_y <= lo_x * hi_y by {
                    apply(integer::multiply_order_nonpositive(lo_x, x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have hi_y * x <= bound by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(x * hi_y, lo_x * hi_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, hi_y * x, bound));
            }
        } else {
            have x < 0 by { close(); }
                have x <= 0 by {
                    apply(integer::lt_le(x, 0));
                }
            have y * x <= lo_y * x by {
                apply(integer::multiply_order_nonpositive(lo_y, y, x));
            }
            if 0 <= lo_y {
                have x * lo_y <= hi_x * lo_y by {
                    apply(integer::multiply_order_nonnegative(x, hi_x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have lo_y * x <= bound by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(x * lo_y, hi_x * lo_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, lo_y * x, bound));
            } else {
                have lo_y < 0 by { close(); }
                have lo_y <= 0 by {
                    apply(integer::lt_le(lo_y, 0));
                }
                have x * lo_y <= lo_x * lo_y by {
                    apply(integer::multiply_order_nonpositive(lo_x, x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have lo_y * x <= bound by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(x * lo_y, lo_x * lo_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, lo_y * x, bound));
            }
        }
    }
}
```

### `integer::int32_positive_is_nonnegative`

```click
theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        apply(integer::lt_le(0, to_integer(value)));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `0 <= value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::add_right_order`

```click
theorem add_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures a + c <= b + c by {
        apply(integer::add_le(a, b, c, c));
    }
}
```

### `integer::int32_less_than_implies_less_equal`

```click
theorem int32_less_than_implies_less_equal(first: int32, last: int32) {
    requires first < last;
    ensures first <= last by {
        apply(integer::lt_le(to_integer(first), to_integer(last)));
        close();
    }
}
```

### `integer::int32_less_than_less_equal_transitive`

```click
theorem int32_less_than_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;
    ensures first < last by {
        have to_integer(first) + 1 <= to_integer(middle) by {
            apply(integer::lt_step_le(to_integer(first), to_integer(middle)));
        }
        have to_integer(first) + 1 <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle), to_integer(last)));
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last)));
        close();
    }
}
```

### `integer::int32_less_equal_less_than_transitive`

```click
theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        have (to_integer(first) + 1) <= (to_integer(middle) + 1) by {
            apply(integer::add_right_order(to_integer(first), to_integer(middle), 1));
        }
        have (to_integer(middle) + 1) <= to_integer(last) by {
            apply(integer::lt_step_le(to_integer(middle), to_integer(last)));
        }
        have (to_integer(first) + 1) <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle) + 1, to_integer(last)));
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last)));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_less_equal_transitive`

```click
theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::le_transitive(to_integer(first), to_integer(middle), to_integer(last)));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `first <= last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_less_than_less_equal_transitive`

```click
theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        have (to_integer(first) + 1) <= to_integer(middle) by {
            apply(integer::lt_step_le(to_integer(first), to_integer(middle)));
        }
        have (to_integer(first) + 1) <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle), to_integer(last)));
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last)));
        close();
    }
}
```

Transitivity of unsigned 64-bit order: `first < middle` and `middle <= last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_less_equal_transitive`

```click
theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::le_transitive(to_integer(first), to_integer(middle), to_integer(last)));
        close();
    }
}
```

Transitivity of unsigned 64-bit order: `first <= middle` and `middle <= last` give `first <= last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::subtract_right_order`

```click
theorem subtract_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures a - c <= b - c by {
        have a + -c <= b + -c by {
            apply(integer::add_right_order(a, b, -c));
        }
        have a - c == a + -c by {
            close();
        }
        have b - c == b + -c by {
            close();
        }
        apply(integer::le_substitute(a + -c, b + -c, a - c, b - c));
    }
}
```

### `integer::lt_le_predecessor`

```click
theorem lt_le_predecessor(a: Integer, b: Integer) {
    requires a < b;
    ensures a <= b - 1 by {
        have a + 1 <= b by {
            apply(integer::lt_step_le(a, b));
        }
        have (a + 1) - 1 <= b - 1 by {
            apply(integer::subtract_right_order(a + 1, b, 1));
        }
        have a == (a + 1) - 1 by { close(); }
        rewrite(a, (a + 1) - 1);
        close();
    }
}
```

### `integer::subtract_left_order`

```click
theorem subtract_left_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures c - b <= c - a by {
        have -b <= -a by {
            apply(integer::negate_order(a, b));
        }
        have -b + c <= -a + c by {
            apply(integer::add_right_order(-b, -a, c));
        }
        have c - b == -b + c by {
            close();
        }
        have c - a == -a + c by {
            close();
        }
        apply(integer::le_substitute(-b + c, -a + c, c - b, c - a));
    }
}
```

### `integer::int32_positive_predecessor_is_nonnegative`

```click
theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        have 0 <= to_integer(value) - 1 by {
            apply(integer::lt_le_predecessor(0, to_integer(value)));
        }
        have -2147483648 <= to_integer(value) - 1 by {
            apply(integer::le_transitive(-2147483648, 0, to_integer(value) - 1));
        }
        have to_integer(value) - 1 <= to_integer(value) by close();
        have to_integer(value) <= 2147483647 by close();
        have to_integer(value) - 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), 2147483647));
        }
        have defined(value - 1) by close();
        apply(integer::int32_subtract_to_integer(value, 1));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `0 <= to_integer(value - 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_positive_predecessor_strictly_decreases`

```click
theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        have 0 <= to_integer(value) - 1 by {
            apply(integer::lt_le_predecessor(0, to_integer(value)));
        }
        have -2147483648 <= to_integer(value) - 1 by {
            apply(integer::le_transitive(-2147483648, 0, to_integer(value) - 1));
        }
        have to_integer(value) - 1 <= to_integer(value) by close();
        have to_integer(value) <= 2147483647 by close();
        have to_integer(value) - 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), 2147483647));
        }
        have defined(value - 1) by close();
        apply(integer::int32_subtract_to_integer(value, 1));
        have to_integer(value) - 1 < to_integer(value) by close();
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value - 1) < to_integer(value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_nonnegative_predecessor_upper_bound`

```click
theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        have 0 - 1 <= to_integer(value) - 1 by {
            apply(integer::subtract_right_order(0, to_integer(value), 1));
        }
        have -2147483648 <= to_integer(value) - 1 by {
            apply(integer::le_transitive(-2147483648, 0 - 1, to_integer(value) - 1));
        }
        have to_integer(value) - 1 <= to_integer(value) by close();
        have to_integer(value) <= 2147483647 by close();
        have to_integer(value) - 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), 2147483647));
        }
        have defined(value - 1) by close();
        apply(integer::int32_subtract_to_integer(value, 1));
        apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), to_integer(bound)));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value - 1) <= to_integer(bound)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_nonnegative_subtract_within_value_is_defined`

```click
theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        have to_integer(amount) - to_integer(amount) <= to_integer(value) - to_integer(amount) by {
            apply(integer::subtract_right_order(to_integer(amount), to_integer(value), to_integer(amount)));
        }
        have 0 <= to_integer(value) - to_integer(amount) by {
            have 0 == to_integer(amount) - to_integer(amount) by close();
            rewrite(0, to_integer(amount) - to_integer(amount));
            close();
        }
        have -2147483648 <= to_integer(value) - to_integer(amount) by {
            apply(integer::le_transitive(-2147483648, 0, to_integer(value) - to_integer(amount)));
        }
        have to_integer(value) - to_integer(amount) <= to_integer(value) - 0 by {
            apply(integer::subtract_left_order(0, to_integer(amount), to_integer(value)));
        }
        have to_integer(value) - 0 <= 2147483647 by {
            have to_integer(value) - 0 == to_integer(value) by close();
            rewrite(to_integer(value) - 0, to_integer(value));
            close();
        }
        have to_integer(value) - to_integer(amount) <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - to_integer(amount), to_integer(value) - 0, 2147483647));
        }
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `defined(value - amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_nonnegative_add_within_max_is_defined`

```click
theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        have to_integer(amount) <= 2147483647 by close();
        have amount <= 2147483647 by close();
        have defined(2147483647 - amount) by {
            apply(integer::int32_nonnegative_subtract_within_value_is_defined(2147483647, amount));
        }
        apply(integer::int32_subtract_to_integer(2147483647, amount));
        have to_integer(value) <= 2147483647 - to_integer(amount) by {
            rewrite(2147483647 - to_integer(amount), to_integer(2147483647 - amount));
            close();
        }
        have to_integer(value) + to_integer(amount) <= (2147483647 - to_integer(amount)) + to_integer(amount) by {
            apply(integer::add_right_order(to_integer(value), 2147483647 - to_integer(amount), to_integer(amount)));
        }
        have to_integer(value) + to_integer(amount) <= 2147483647 by {
            have 2147483647 == (2147483647 - to_integer(amount)) + to_integer(amount) by close();
            rewrite(2147483647, (2147483647 - to_integer(amount)) + to_integer(amount));
            close();
        }
        have -2147483648 <= to_integer(value) by close();
        have -2147483648 + 0 <= to_integer(value) + to_integer(amount) by {
            apply(integer::add_le(-2147483648, to_integer(value), 0, to_integer(amount)));
        }
        have -2147483648 <= to_integer(value) + to_integer(amount) by {
            have -2147483648 == -2147483648 + 0 by close();
            rewrite(-2147483648, -2147483648 + 0);
            close();
        }
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `defined(value + amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_positive_predecessor_strictly_decreases`

```click
theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        have to_integer(0u32) < to_integer(value) by close();
        apply(integer::lt_step_le(0, to_integer(value)));
        have to_integer(1u32) <= to_integer(value) by close();
        have 1u32 <= value by close();
        apply(integer::uint32_subtract_to_integer(value, 1u32));
        have to_integer(value) - 1 < to_integer(value) by close();
        rewrite(to_integer(value - 1u32), to_integer(value) - to_integer(1u32));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value - 1u32) < to_integer(value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_increment_upper_bound`

```click
theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 4294967295 by close();
        have to_integer(value) + 1 <= 4294967295 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 4294967295));
        }
        have to_integer(value) + to_integer(1u32) <= 4294967295 by close();
        apply(integer::uint32_add_to_integer(value, 1u32));
        rewrite(to_integer(value + 1u32), to_integer(value) + to_integer(1u32));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value + 1u32) <= to_integer(upper)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_less_than_implies_positive_difference`

```click
theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have (to_integer(value) + 1) - to_integer(value) <= to_integer(upper) - to_integer(value) by {
            apply(integer::subtract_right_order(to_integer(value) + 1, to_integer(upper), to_integer(value)));
        }
        have 0 + 1 <= to_integer(upper) - to_integer(value) by {
            have 0 + 1 == (to_integer(value) + 1) - to_integer(value) by close();
            rewrite(0 + 1, (to_integer(value) + 1) - to_integer(value));
            close();
        }
        apply(integer::step_le_lt(0, to_integer(upper) - to_integer(value)));
        have to_integer(value) <= to_integer(upper) by {
            apply(integer::lt_le(to_integer(value), to_integer(upper)));
        }
        have value <= upper by close();
        apply(integer::uint32_subtract_to_integer(upper, value));
        rewrite(to_integer(upper - value), to_integer(upper) - to_integer(value));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `0 < to_integer(upper - value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::subtract_le`

```click
theorem subtract_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires d <= c;
    ensures a - c <= b - d by {
        have a - c <= b - c by {
            apply(integer::subtract_right_order(a, b, c));
        }
        have b - c <= b - d by {
            apply(integer::subtract_left_order(d, c, b));
        }
        apply(integer::le_transitive(a - c, b - c, b - d));
    }
}
```

### `integer::negate_multiply`

```click
theorem negate_multiply(a: Integer, b: Integer) {
    ensures -a * b == -(a * b) by {
        have b * -a == -(b * a) by {
            apply(integer::multiply_negate(b, a));
        }
        have -a * b == b * -a by {
            apply(integer::multiply_commutative(-a, b));
        }
        have a * b == b * a by {
            apply(integer::multiply_commutative(a, b));
        }
        rewrite(-a * b, b * -a);
        rewrite(a * b, b * a);
        close();
    }
}
```

### `integer::equal_negate`

```click
theorem equal_negate(a: Integer, b: Integer) {
    requires a == b;
    ensures -a == -b by {
        rewrite(a, b);
        close();
    }
}
```

### `integer::sum_commute`

```click
theorem sum_commute(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
    ensures a == c + b by {
        have c + b == b + c by {
            close();
        }
        rewrite(c + b, b + c);
        close();
    }
}
```

### `integer::sum_difference`

```click
theorem sum_difference(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
    ensures a + -c == b by {
        have a + -c == (b + c) + -c by {
            apply(integer::equal_add(a, b + c, -c, -c));
        }
        have b == (b + c) + -c by {
            close();
        }
        rewrite(b, (b + c) + -c);
        close();
    }
    ensures -b == -a + c by {
        have a + -c == b by {
            have a + -c == (b + c) + -c by {
                apply(integer::equal_add(a, b + c, -c, -c));
            }
            have b == (b + c) + -c by {
                close();
            }
            rewrite(b, (b + c) + -c);
            close();
        }
        have -(a + -c) == -b by {
            apply(integer::equal_negate(a + -c, b));
        }
        have -a + c == -(a + -c) by {
            close();
        }
        rewrite(-a + c, -(a + -c));
        close();
    }
}
```

### `integer::positive_divisor_quotient_upper_rounded`

```click
theorem positive_divisor_quotient_upper_rounded(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires n <= (bound * d) + (d - 1);
    ensures truncating_quotient(n, d) <= bound by {
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 0 <= truncating_remainder(n, d) by {
            apply(integer::nonnegative_dividend_remainder(n, d));
        }
        have 0 + (truncating_quotient(n, d) * d) <= truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::add_le(0, truncating_remainder(n, d), (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d)));
        }
        have (truncating_quotient(n, d) * d) <= n by {
            have (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d) by {
                close();
            }
            have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
                close();
            }
            apply(integer::le_substitute(0 + (truncating_quotient(n, d) * d), truncating_remainder(n, d) + (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d), n));
        }
        have (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1) by {
            apply(integer::le_transitive((truncating_quotient(n, d) * d), n, (bound * d) + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        apply(integer::round_down_le(truncating_quotient(n, d), bound, d, (d - 1)));
    }
}
```

### `integer::positive_divisor_quotient_lower_rounded`

```click
theorem positive_divisor_quotient_lower_rounded(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
    requires (bound * d) - (d - 1) <= n;
    ensures bound <= truncating_quotient(n, d) by {
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have truncating_remainder(n, d) <= 0 by {
            apply(integer::nonpositive_dividend_remainder(n, d));
        }
        have truncating_remainder(n, d) + (truncating_quotient(n, d) * d) <= 0 + (truncating_quotient(n, d) * d) by {
            apply(integer::add_le(truncating_remainder(n, d), 0, (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d)));
        }
        have n <= (truncating_quotient(n, d) * d) by {
            have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
                close();
            }
            have (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d) by {
                close();
            }
            apply(integer::le_substitute(truncating_remainder(n, d) + (truncating_quotient(n, d) * d), 0 + (truncating_quotient(n, d) * d), n, (truncating_quotient(n, d) * d)));
        }
        have (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d) by {
            apply(integer::le_transitive((bound * d) - (d - 1), n, (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)) by {
            apply(integer::negate_order((bound * d) - (d - 1), (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
            apply(integer::negate_multiply(truncating_quotient(n, d), d));
        }
        have -bound * d == -(bound * d) by {
            apply(integer::negate_multiply(bound, d));
        }
        have -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1) by {
            have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
                rewrite(-(truncating_quotient(n, d)) * d, -(truncating_quotient(n, d) * d));
                close();
            }
            have -bound * d + (d - 1) == -((bound * d) - (d - 1)) by {
                rewrite(-bound * d, -(bound * d));
                close();
            }
            apply(integer::le_substitute(-(truncating_quotient(n, d) * d), -((bound * d) - (d - 1)), -(truncating_quotient(n, d)) * d, -bound * d + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        have -(truncating_quotient(n, d)) <= -bound by {
            apply(integer::round_down_le(-(truncating_quotient(n, d)), -bound, d, (d - 1)));
        }
        have -(-bound) <= -(-(truncating_quotient(n, d))) by {
            apply(integer::negate_order(-(truncating_quotient(n, d)), -bound));
        }
        have bound == -(-bound) by {
            close();
        }
        have truncating_quotient(n, d) == -(-(truncating_quotient(n, d))) by {
            close();
        }
        apply(integer::le_substitute(-(-bound), -(-(truncating_quotient(n, d))), bound, truncating_quotient(n, d)));
    }
}
```

### `integer::nonnegative_dividend_remainder_upper`

```click
theorem nonnegative_dividend_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    ensures truncating_remainder(n, d) <= n by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have 0 <= d by {
            apply(integer::lt_le(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 0 * d == 0 by {
            close();
        }
        have 0 * d <= n by {
            rewrite(0 * d, 0);
            close();
        }
        have 0 <= truncating_quotient(n, d) by {
            apply(integer::positive_divisor_quotient_lower(n, d, 0));
        }
        have 0 * d <= (truncating_quotient(n, d) * d) by {
            apply(integer::multiply_order_nonnegative(0, truncating_quotient(n, d), d));
        }
        have 0 <= (truncating_quotient(n, d) * d) by {
            rewrite(0, 0 * d);
            close();
        }
        have 0 + truncating_remainder(n, d) <= (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::add_le(0, (truncating_quotient(n, d) * d), truncating_remainder(n, d), truncating_remainder(n, d)));
        }
        have truncating_remainder(n, d) == 0 + truncating_remainder(n, d) by {
            close();
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            close();
        }
        apply(integer::le_substitute(0 + truncating_remainder(n, d), (truncating_quotient(n, d) * d) + truncating_remainder(n, d), truncating_remainder(n, d), n));
    }
}
```

### `integer::nonpositive_dividend_remainder_lower`

```click
theorem nonpositive_dividend_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
    ensures n <= truncating_remainder(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have 0 <= d by {
            apply(integer::lt_le(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 0 * d == 0 by {
            close();
        }
        have n <= 0 * d by {
            rewrite(0 * d, 0);
            close();
        }
        have truncating_quotient(n, d) <= 0 by {
            apply(integer::positive_divisor_quotient_upper(n, d, 0));
        }
        have (truncating_quotient(n, d) * d) <= 0 * d by {
            apply(integer::multiply_order_nonnegative(truncating_quotient(n, d), 0, d));
        }
        have (truncating_quotient(n, d) * d) <= 0 by {
            rewrite(0, 0 * d);
            close();
        }
        have (truncating_quotient(n, d) * d) + truncating_remainder(n, d) <= 0 + truncating_remainder(n, d) by {
            apply(integer::add_le((truncating_quotient(n, d) * d), 0, truncating_remainder(n, d), truncating_remainder(n, d)));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            close();
        }
        have truncating_remainder(n, d) == 0 + truncating_remainder(n, d) by {
            close();
        }
        apply(integer::le_substitute((truncating_quotient(n, d) * d) + truncating_remainder(n, d), 0 + truncating_remainder(n, d), n, truncating_remainder(n, d)));
    }
}
```

### `integer::quotient_upper_interval_nonnegative`

```click
theorem quotient_upper_interval_nonnegative(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= bound;
    requires endpoint <= d;
    requires n <= numerator_bound;
    requires numerator_bound <= bound * endpoint + (endpoint - 1);
    ensures truncating_quotient(n, d) <= bound by {
        have bound * endpoint <= bound * d by {
            have endpoint * bound <= d * bound by {
                apply(integer::multiply_order_nonnegative(endpoint, d, bound));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            apply(integer::le_substitute(endpoint * bound, d * bound, bound * endpoint, bound * d));
        }
        have endpoint - 1 <= d - 1 by {
            apply(integer::subtract_right_order(endpoint, d, 1));
        }
        have bound * endpoint + (endpoint - 1) <= bound * d + (d - 1) by {
            apply(integer::add_le(bound * endpoint, bound * d, endpoint - 1, d - 1));
        }
        have numerator_bound <= bound * d + (d - 1) by {
            apply(integer::le_transitive(numerator_bound, bound * endpoint + (endpoint - 1), bound * d + (d - 1)));
        }
        have n <= bound * d + (d - 1) by {
            apply(integer::le_transitive(n, numerator_bound, bound * d + (d - 1)));
        }
        if n <= 0 {
            have 0 * d == 0 by {
                close();
            }
            have n <= 0 * d by {
                rewrite(0 * d, 0);
                close();
            }
            have truncating_quotient(n, d) <= 0 by {
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
            }
            apply(integer::le_transitive(truncating_quotient(n, d), 0, bound));
        } else {
            have 0 < n by {
                close();
            }
            have 0 <= n by {
                apply(integer::lt_le(0, n));
            }
            apply(integer::positive_divisor_quotient_upper_rounded(n, d, bound));
        }
    }
}
```

### `integer::quotient_lower_interval_nonpositive`

```click
theorem quotient_lower_interval_nonpositive(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound <= 0;
    requires endpoint <= d;
    requires numerator_bound <= n;
    requires bound * endpoint - (endpoint - 1) <= numerator_bound;
    ensures bound <= truncating_quotient(n, d) by {
        have bound * d <= bound * endpoint by {
            have d * bound <= endpoint * bound by {
                apply(integer::multiply_order_nonpositive(endpoint, d, bound));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            apply(integer::le_substitute(d * bound, endpoint * bound, bound * d, bound * endpoint));
        }
        have endpoint - 1 <= d - 1 by {
            apply(integer::subtract_right_order(endpoint, d, 1));
        }
        have -(d - 1) <= -(endpoint - 1) by {
            apply(integer::negate_order(endpoint - 1, d - 1));
        }
        have bound * d + -(d - 1) <= bound * endpoint + -(endpoint - 1) by {
            apply(integer::add_le(bound * d, bound * endpoint, -(d - 1), -(endpoint - 1)));
        }
        have bound * d - (d - 1) <= bound * endpoint - (endpoint - 1) by {
            have bound * d - (d - 1) == bound * d + -(d - 1) by {
                close();
            }
            have bound * endpoint - (endpoint - 1) == bound * endpoint + -(endpoint - 1) by {
                close();
            }
            apply(integer::le_substitute(bound * d + -(d - 1), bound * endpoint + -(endpoint - 1), bound * d - (d - 1), bound * endpoint - (endpoint - 1)));
        }
        have bound * d - (d - 1) <= numerator_bound by {
            apply(integer::le_transitive(bound * d - (d - 1), bound * endpoint - (endpoint - 1), numerator_bound));
        }
        have bound * d - (d - 1) <= n by {
            apply(integer::le_transitive(bound * d - (d - 1), numerator_bound, n));
        }
        if 0 <= n {
            have 0 * d == 0 by {
                close();
            }
            have 0 * d <= n by {
                rewrite(0 * d, 0);
                close();
            }
            have 0 <= truncating_quotient(n, d) by {
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
            }
            apply(integer::le_transitive(bound, 0, truncating_quotient(n, d)));
        } else {
            have n < 0 by {
                close();
            }
            have n <= 0 by {
                apply(integer::lt_le(n, 0));
            }
            apply(integer::positive_divisor_quotient_lower_rounded(n, d, bound));
        }
    }
}
```

### `integer::quotient_upper_interval_negative`

```click
theorem quotient_upper_interval_negative(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound <= 0;
    requires d <= endpoint;
    requires n <= numerator_bound;
    requires numerator_bound <= bound * endpoint;
    ensures truncating_quotient(n, d) <= bound by {
        have bound * endpoint <= bound * d by {
            have endpoint * bound <= d * bound by {
                apply(integer::multiply_order_nonpositive(d, endpoint, bound));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            apply(integer::le_substitute(endpoint * bound, d * bound, bound * endpoint, bound * d));
        }
        have n <= bound * endpoint by {
            apply(integer::le_transitive(n, numerator_bound, bound * endpoint));
        }
        have n <= bound * d by {
            apply(integer::le_transitive(n, bound * endpoint, bound * d));
        }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
    }
}
```

### `integer::quotient_lower_interval_positive`

```click
theorem quotient_lower_interval_positive(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= bound;
    requires d <= endpoint;
    requires numerator_bound <= n;
    requires bound * endpoint <= numerator_bound;
    ensures bound <= truncating_quotient(n, d) by {
        have bound * d <= bound * endpoint by {
            have d * bound <= endpoint * bound by {
                apply(integer::multiply_order_nonnegative(d, endpoint, bound));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            apply(integer::le_substitute(d * bound, endpoint * bound, bound * d, bound * endpoint));
        }
        have bound * d <= numerator_bound by {
            apply(integer::le_transitive(bound * d, bound * endpoint, numerator_bound));
        }
        have bound * d <= n by {
            apply(integer::le_transitive(bound * d, numerator_bound, n));
        }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
    }
}
```

### `integer::remainder_lower_from_dividend`

```click
theorem remainder_lower_from_dividend(n: Integer, d: Integer, numerator_bound: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires numerator_bound <= n;
    requires bound <= numerator_bound;
    requires bound <= 0;
    ensures bound <= truncating_remainder(n, d) by {
        if n <= 0 {
            have n <= truncating_remainder(n, d) by {
                apply(integer::nonpositive_dividend_remainder_lower(n, d));
            }
            have bound <= n by {
                apply(integer::le_transitive(bound, numerator_bound, n));
            }
            apply(integer::le_transitive(bound, n, truncating_remainder(n, d)));
        } else {
            have 0 < n by {
                close();
            }
            have 0 <= n by {
                apply(integer::lt_le(0, n));
            }
            have 0 <= truncating_remainder(n, d) by {
                apply(integer::nonnegative_dividend_remainder(n, d));
            }
            apply(integer::le_transitive(bound, 0, truncating_remainder(n, d)));
        }
    }
}
```

### `integer::remainder_lower_from_divisor`

```click
theorem remainder_lower_from_divisor(n: Integer, d: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires d <= endpoint;
    requires bound <= 1 - endpoint;
    ensures bound <= truncating_remainder(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have 1 - d <= truncating_remainder(n, d) by {
            apply(integer::positive_divisor_remainder_lower(n, d));
        }
        have 1 - endpoint <= 1 - d by {
            apply(integer::subtract_left_order(d, endpoint, 1));
        }
        have bound <= 1 - d by {
            apply(integer::le_transitive(bound, 1 - endpoint, 1 - d));
        }
        apply(integer::le_transitive(bound, 1 - d, truncating_remainder(n, d)));
    }
}
```

### `integer::remainder_upper_from_dividend`

```click
theorem remainder_upper_from_dividend(n: Integer, d: Integer, numerator_bound: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= numerator_bound;
    requires numerator_bound <= bound;
    requires 0 <= bound;
    ensures truncating_remainder(n, d) <= bound by {
        if 0 <= n {
            have truncating_remainder(n, d) <= n by {
                apply(integer::nonnegative_dividend_remainder_upper(n, d));
            }
            have n <= bound by {
                apply(integer::le_transitive(n, numerator_bound, bound));
            }
            apply(integer::le_transitive(truncating_remainder(n, d), n, bound));
        } else {
            have n < 0 by {
                close();
            }
            have n <= 0 by {
                apply(integer::lt_le(n, 0));
            }
            have truncating_remainder(n, d) <= 0 by {
                apply(integer::nonpositive_dividend_remainder(n, d));
            }
            apply(integer::le_transitive(truncating_remainder(n, d), 0, bound));
        }
    }
}
```

### `integer::remainder_upper_from_divisor`

```click
theorem remainder_upper_from_divisor(n: Integer, d: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires d <= endpoint;
    requires endpoint - 1 <= bound;
    ensures truncating_remainder(n, d) <= bound by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have truncating_remainder(n, d) <= d - 1 by {
            apply(integer::positive_divisor_remainder_upper(n, d));
        }
        have d - 1 <= endpoint - 1 by {
            apply(integer::subtract_right_order(d, endpoint, 1));
        }
        have truncating_remainder(n, d) <= endpoint - 1 by {
            apply(integer::le_transitive(truncating_remainder(n, d), d - 1, endpoint - 1));
        }
        apply(integer::le_transitive(truncating_remainder(n, d), endpoint - 1, bound));
    }
}
```

### `integer::small_remainder_interval`

```click
theorem small_remainder_interval(n: Integer, d: Integer, lo_n: Integer, hi_n: Integer, endpoint: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires endpoint <= d;
    requires lo_n <= n;
    requires n <= hi_n;
    requires 1 - endpoint <= lo_n;
    requires hi_n <= endpoint - 1;
    ensures truncating_remainder(n, d) == n by {
        have 0 * endpoint - (endpoint - 1) <= lo_n by {
            have 0 * endpoint - (endpoint - 1) == 1 - endpoint by {
                close();
            }
            rewrite(0 * endpoint - (endpoint - 1), 1 - endpoint);
            close();
        }
        have hi_n <= 0 * endpoint + (endpoint - 1) by {
            have 0 * endpoint + (endpoint - 1) == endpoint - 1 by {
                close();
            }
            rewrite(0 * endpoint + (endpoint - 1), endpoint - 1);
            close();
        }
        have 0 <= truncating_quotient(n, d) by {
            apply(integer::quotient_lower_interval_nonpositive(n, d, lo_n, endpoint, 0));
        }
        have truncating_quotient(n, d) <= 0 by {
            apply(integer::quotient_upper_interval_nonnegative(n, d, hi_n, endpoint, 0));
        }
        have truncating_quotient(n, d) == 0 by {
            apply(integer::le_antisymmetric(truncating_quotient(n, d), 0));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have truncating_remainder(n, d) == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            rewrite(truncating_quotient(n, d), 0);
            close();
        }
        have (truncating_quotient(n, d) * d) + truncating_remainder(n, d) == n by {
            close();
        }
        apply(integer::equal_substitute((truncating_quotient(n, d) * d) + truncating_remainder(n, d), n, truncating_remainder(n, d), n));
    }
}
```

### `integer::nonzero_from_one`

```click
theorem nonzero_from_one(d: Integer) {
    requires 1 <= d;
    let one: Integer = 1;
    ensures d != 0 by {
        if d == 0 {
            have one <= 0 by {
                apply(integer::le_substitute(one, d, one, 0));
            }
            contradiction(one <= 0);
        } else { close(); }
    }
}
```

### `integer::nonzero_from_negative_one`

```click
theorem nonzero_from_negative_one(d: Integer) {
    requires d <= -1;
    let zero: Integer = 0;
    ensures d != 0 by {
        if d == 0 {
            have zero <= -1 by {
                apply(integer::le_substitute(d, -1, zero, -1));
            }
            contradiction(zero <= -1);
        } else { close(); }
    }
}
```

### `integer::quotient_negate_divisor`

```click
theorem quotient_negate_divisor(n: Integer, d: Integer) {
    requires d != 0;
    requires -d != 0;
    ensures truncating_quotient(n, d) == -truncating_quotient(n, -d);
}
```

### `integer::remainder_negate_divisor`

```click
theorem remainder_negate_divisor(n: Integer, d: Integer) {
    requires d != 0;
    requires -d != 0;
    ensures truncating_remainder(n, d) == truncating_remainder(n, -d);
}
```

### `integer::scaled_product_bounds`

```click
theorem scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        have lower * amount <= value * amount by {
            apply(integer::multiply_order_nonnegative(lower, value, amount));
        }
        have size * lower <= amount * lower by {
            apply(integer::multiply_order_nonpositive(amount, size, lower));
        }
        have lower * size == size * lower by { apply(integer::multiply_commutative(lower, size)); }
        have lower * amount == amount * lower by { apply(integer::multiply_commutative(lower, amount)); }
        have lower * size <= lower * amount by {
            rewrite(lower * size, size * lower);
            rewrite(lower * amount, amount * lower);
            close();
        }
        apply(integer::le_transitive(lower * size, lower * amount, value * amount));
    }
    ensures value * amount <= upper * size by {
        have value * amount <= upper * amount by {
            apply(integer::multiply_order_nonnegative(value, upper, amount));
        }
        have amount * upper <= size * upper by {
            apply(integer::multiply_order_nonnegative(amount, size, upper));
        }
        have upper * amount == amount * upper by { apply(integer::multiply_commutative(upper, amount)); }
        have upper * size == size * upper by { apply(integer::multiply_commutative(upper, size)); }
        have upper * amount <= upper * size by {
            rewrite(upper * amount, amount * upper);
            rewrite(upper * size, size * upper);
            close();
        }
        apply(integer::le_transitive(value * amount, upper * amount, upper * size));
    }
}
```

### `integer::int32_remainder_to_integer`

```click
theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Connects a defined signed machine remainder to mathematical truncation. Native definedness excludes both a zero divisor and `INT32_MIN % -1`; a nonzero mathematical divisor alone does not establish that the C operation is defined.

### `integer::uint32_from_le_bytes`

```click
theorem uint32_from_le_bytes(p: uint32*) {
    requires little_endian();
    views p[0..1];
    requires defined(p[0]);
    ensures p[0] ==
        (((p as (uint8 *))[0] as uint32) |
         ((p as (uint8 *))[1] as uint32) << 8u32 |
         ((p as (uint8 *))[2] as uint32) << 16u32 |
         ((p as (uint8 *))[3] as uint32) << 24u32);
}
```

Relates one readable unsigned 32-bit object to its four character representation
bytes at the same point. `little_endian()` is a built-in target fact;
C proofs receive it only from a little-endian execution environment. Pure
theorems must state it as a premise. The rule does not grant read permission,
initialize memory, or reinterpret pointer representations. Its kernel
constructor constructs five reads and a fixed packing expression without
searching memory history. Applications retain the named lemma in expansion.

Checked use: [`integer_uint32_from_le_bytes_initialization.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_uint32_from_le_bytes_initialization.md).

## `click::permutation`

Source: `library/permutation.click`, `import click::permutation;`.

### `permutation::count`

```click
function count<T>(p: T*, lo: int32, hi: int32, x: T) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of elements equal to `x` in the half-open range `lo..hi` of the array reference `p`. It is generic over the element type: `T` is inferred from `p`, an `int32[]` or `uint8[]` array ref (a pure-function `T*` parameter is an array ref), and `x` must have that same type.

**Kind:** generic function. Parameter types, requirements, and guarantees are normative in the declaration above. The bounds stay `int32`, as `bytes::count`'s do.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. [`mdtests/stdlib_permutation_count_over_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_over_bytes.md) counts a `uint8` buffer, [`mdtests/stdlib_permutation_count_over_bytes_rejects_overwrite.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_over_bytes_rejects_overwrite.md) refuses an overwrite as a byte permutation, and [`mdtests/stdlib_permutation_count_rejects_mixed_element_types.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_rejects_mixed_element_types.md) refuses an `int32` value counted in a `uint8` buffer.

### `permutation::two_indicator_counts_commute`

```click
theorem two_indicator_counts_commute(a: Bool, b: Bool) {
    ensures (0 + (if a { 1 } else { 0 }) + (if b { 1 } else { 0 })) ==
            (0 + (if b { 1 } else { 0 }) + (if a { 1 } else { 0 })) by {
        if a {
            have (if a { 1 } else { 0 }) == 1 by close();
            rewrite((if a { 1 } else { 0 }), 1);
            if b {
                have (if b { 1 } else { 0 }) == 1 by close();
                rewrite((if b { 1 } else { 0 }), 1);
                close();
            } else {
                have (if b { 1 } else { 0 }) == 0 by close();
                rewrite((if b { 1 } else { 0 }), 0);
                close();
            }
        } else {
            have (if a { 1 } else { 0 }) == 0 by close();
            rewrite((if a { 1 } else { 0 }), 0);
            if b {
                have (if b { 1 } else { 0 }) == 1 by close();
                rewrite((if b { 1 } else { 0 }), 1);
                close();
            } else {
                have (if b { 1 } else { 0 }) == 0 by close();
                rewrite((if b { 1 } else { 0 }), 0);
                close();
            }
        }
    }
}
```

Interchanges the two Boolean indicators in the unfolded two-element count.
The equality keeps the fold's initial zero and uses native `int32` addition.
Both the integer and byte swap proofs apply it after unfolding the counts.
[`compare_swap2_permutation.md`](https://github.com/clicklang/click/blob/master/mdtests/compare_swap2_permutation.md)
[`stdlib_permutation_count_over_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_over_bytes.md)

### `permutation::permutation`

```click
predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        permutation::count(a, lo, hi, x) == permutation::count(b, lo, hi, x)
    }
}
```

**Meaning:** States that `a` and `b` contain every `int32` value the same number of times in `lo..hi`. Unfolding exposes equality of two `count` calls under a universal quantifier.

**Limit:** the predicate is stated over `int32[]` only. A generic form would quantify over its element type, `forall (x: T)`, and a quantifier's type must be a concrete C, `Integer` or algebraic type; the parser refuses a type parameter there. A permutation over another element type is a file predicate over the generic `permutation::count`, as `byte_permutation` in [`mdtests/stdlib_permutation_count_over_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_over_bytes.md) is.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(permutation::permutation(args))` when a proof needs the predicate body.

## `click::bytes`

Source: `library/bytes.click`, `import click::bytes;`, or brought by `click::c::string`, in which case a sidecar without the import writes the full `click::bytes::` path.

### `bytes::count`

```click
function count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of bytes equal to `value` in the half-open range `lo..hi`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `bytes::equal`

```click
predicate equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    (0u64..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}
```

**Meaning:** States that the `len` bytes starting at `left_lo` and `right_lo` are pairwise equal. Offsets and lengths are `size_t` values.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::equal(args))` when a proof needs the predicate body.

### `bytes::equal_range`

```click
predicate equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}
```

**Meaning:** States that `left` and `right` are pairwise equal throughout the same half-open range `lo..hi`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::equal_range(args))` when a proof needs the predicate body.

### `bytes::all_equal`

```click
predicate all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that every byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::all_equal(args))` when a proof needs the predicate body.

### `bytes::contains`

```click
predicate contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that at least one byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::contains(args))` when a proof needs the predicate body.

### `bytes::all_not_equal`

```click
predicate all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}
```

**Meaning:** States that every byte in `lo..hi` differs from `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::all_not_equal(args))` when a proof needs the predicate body.

### `bytes::comparison`

```click
predicate comparison(left: uint8[], right: uint8[], length: uint64, cmp: int32) {
    (cmp == 0 implies bytes::equal(left, 0u64, right, 0u64, length)) and
    (cmp != 0 implies not bytes::equal(left, 0u64, right, 0u64, length)) and
    forall (k: uint64) {
        k < length and bytes::equal_range(left, right, 0u64, k) implies
            (left[k] < right[k] implies cmp < 0) and
            (right[k] < left[k] implies cmp > 0)
    }
}
```

**Meaning:** Describes a signed comparison of the first `length` bytes. Zero means the ranges are equal and nonzero means they differ. At the first differing unsigned byte, a smaller left byte requires a negative result and a larger left byte requires a positive result. The magnitude is unspecified.

**Kind:** predicate. The declaration above is normative.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) applies the comparison laws. C ordering clients are checked in [`mdtests/memcmp_orders_the_first_differing_byte.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_the_first_differing_byte.md) and [`mdtests/memcmp_orders_after_equal_prefix.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_after_equal_prefix.md).

### `bytes::comparison_negative_after_prefix`

```click
theorem comparison_negative_after_prefix(left: uint8[], right: uint8[], length: uint64, first: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires first < length;
    requires bytes::equal_range(left, right, 0u64, first);
    requires left[first] < right[first];
    ensures cmp < 0 by {
        unfold(bytes::comparison(left, right, length, cmp));
        instantiate(forall (k: uint64) {
            k < length and bytes::equal_range(left, right, 0u64, k) implies
                (left[k] < right[k] implies cmp < 0) and
                (right[k] < left[k] implies cmp > 0)
        }, first);
        close();
    }
}
```

**Meaning:** An equal prefix ending at `first`, followed by a smaller left byte within the compared range, forces a negative comparison. This is a checked theorem; the author supplies the first-difference index.

**Kind:** proved theorem. The declaration above is normative.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) applies the comparison laws. C ordering clients are checked in [`mdtests/memcmp_orders_the_first_differing_byte.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_the_first_differing_byte.md) and [`mdtests/memcmp_orders_after_equal_prefix.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_after_equal_prefix.md).

### `bytes::comparison_positive_after_prefix`

```click
theorem comparison_positive_after_prefix(left: uint8[], right: uint8[], length: uint64, first: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires first < length;
    requires bytes::equal_range(left, right, 0u64, first);
    requires right[first] < left[first];
    ensures cmp > 0 by {
        unfold(bytes::comparison(left, right, length, cmp));
        instantiate(forall (k: uint64) {
            k < length and bytes::equal_range(left, right, 0u64, k) implies
                (left[k] < right[k] implies cmp < 0) and
                (right[k] < left[k] implies cmp > 0)
        }, first);
        close();
    }
}
```

**Meaning:** An equal prefix ending at `first`, followed by a larger left byte within the compared range, forces a positive comparison. This is a checked theorem.

**Kind:** proved theorem. The declaration above is normative.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) applies the comparison laws. C ordering clients are checked in [`mdtests/memcmp_orders_the_first_differing_byte.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_the_first_differing_byte.md) and [`mdtests/memcmp_orders_after_equal_prefix.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_after_equal_prefix.md).

### `bytes::comparison_zero_when_equal`

```click
theorem comparison_zero_when_equal(left: uint8[], right: uint8[], length: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires bytes::equal(left, 0u64, right, 0u64, length);
    ensures cmp == 0 by {
        unfold(bytes::comparison(left, right, length, cmp));
        close();
    }
}
```

**Meaning:** Equal compared ranges force a zero result. This is a checked consequence of `bytes::comparison`, including the empty-range case.

**Kind:** proved theorem. The declaration above is normative.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) applies the comparison laws. C ordering clients are checked in [`mdtests/memcmp_orders_the_first_differing_byte.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_the_first_differing_byte.md) and [`mdtests/memcmp_orders_after_equal_prefix.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_orders_after_equal_prefix.md).

## `click::c::stdarg`

Source: `library/c/stdarg.click`. A contract that declares `...args` brings
it in.

### `VarArg`

```click
spec enum VarArg {
    Int(int32),
    UInt(uint32),
    Long(int64),
    ULong(uint64),
}
```

One variable argument of a C call after the default argument promotions. A
variadic function's `extern` contract receives a call's variable arguments
as its last parameter, `...args`, a `List<VarArg>` with the first argument
first; see [variadic calls](../language/c.md#variadic-calls).

**Verified use:** [`mdtests/a_variadic_contract_reads_its_variable_arguments.md`](https://github.com/clicklang/click/blob/master/mdtests/a_variadic_contract_reads_its_variable_arguments.md).

## `click::c::stdio`

Source: `library/c/stdio.click`. The sidecar can import the module or
select names such as `import click::c::stdio::{stream, write_requests};`.

### `WriteAttempt` and `stream`

```click
spec enum WriteAttempt {
    Attempt(List<uint8>, int32),
}

abstract resource stream(file: void*) {
    field write_history: List<WriteAttempt>;
}
```

A write attempt records its requested bytes and the return value from the
write. For the modeled `printf` and `fprintf` calls, a nonnegative result
means the stream accepted the entire request. A negative result signals an
error and may accompany partial output. The latest attempt is at the head of
the history. [Hosted startup](../language/c.md#hosted-standard-output)
supplies the standard output stream with an empty history.

### `stdio::write_requests`

```click
function write_requests(history: List<WriteAttempt>) -> List<List<uint8>>
    decreases history
{
    match history {
        List::Nil => List<List<uint8>>::Nil,
        List::Cons(attempt, tail) => match attempt {
            WriteAttempt::Attempt(bytes, _) =>
                List<List<uint8>>::Cons(bytes, stdio::write_requests(tail)),
        },
    }
}
```

Returns the requested byte lists in history order, regardless of their
outcomes. Verified in [`printf_and_fprintf_share_the_streams_write_history.md`](https://github.com/clicklang/click/blob/master/mdtests/printf_and_fprintf_share_the_streams_write_history.md).

### `stdio::format_output`, `stdio::format_length` and `stdio::literal_format`

```click
function format_output(s: uint8[], k: uint64, remaining: int32) -> List<uint8>
    decreases remaining
{
    if remaining <= 0 {
        List<uint8>::Nil
    } else {
        if s[k] == 37u8 {
            if remaining >= 2 {
                List<uint8>::Cons(37u8, stdio::format_output(s, k + 2u64, remaining - 2))
            } else {
                List<uint8>::Nil
            }
        } else {
            List<uint8>::Cons(s[k], stdio::format_output(s, k + 1u64, remaining - 1))
        }
    }
}
```

```click
function format_length(s: uint8[], k: uint64, remaining: int32, count: int32) -> int32
    decreases remaining
{
    if remaining <= 0 {
        count
    } else {
        if s[k] == 37u8 {
            if remaining >= 2 {
                stdio::format_length(s, k + 2u64, remaining - 2, count + 1)
            } else {
                count
            }
        } else {
            stdio::format_length(s, k + 1u64, remaining - 1, count + 1)
        }
    }
}
```

```click
function literal_format(s: uint8[], k: uint64, remaining: int32) -> Bool
    decreases remaining
{
    if remaining <= 0 {
        true
    } else {
        if s[k] == 37u8 {
            if remaining >= 2 {
                if s[k + 1u64] == 37u8 {
                    stdio::literal_format(s, k + 2u64, remaining - 2)
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            stdio::literal_format(s, k + 1u64, remaining - 1)
        }
    }
}
```

The characters an `fprintf` format of ordinary characters and `%%` writes,
from `remaining` bytes at `k`: each `%%` writes one `%`. `format_length`
counts them onto `count`, so evaluating it over a format adds one to a known
value at each character. `literal_format` holds when the bytes are ordinary
characters and `%%` only, which the
[`fprintf` contract](../language/c.md#formatted-output) requires. Each
recurses on an `int32` measure; `close()` evaluates them over a string literal
one level at a time. Verified in [`printf_and_fprintf_share_the_streams_write_history.md`](https://github.com/clicklang/click/blob/master/mdtests/printf_and_fprintf_share_the_streams_write_history.md) and [`fprintf_refuses_a_format_that_converts.md`](https://github.com/clicklang/click/blob/master/mdtests/fprintf_refuses_a_format_that_converts.md).

### Decimal formatting

`click::c::stdio` states the characters C's `printf` family writes for an
integer. The C front end writes the contract of each `snprintf` call with a
string-literal format with these functions
([formatted output](../language/c.md#formatted-output)). The theorems
`stdio::decimal_length_n` and `stdio::pow10_e` evaluate them for the
32-bit values `%u` and `%d` convert.

### `stdio::pow10`

```click
function pow10(e: uint64) -> uint64 {
    (if e == 0u64 { 1u64 } else { 0u64 }) + (if e == 1u64 { 10u64 } else { 0u64 }) + (if e == 2u64 { 100u64 } else { 0u64 }) + (if e == 3u64 { 1000u64 } else { 0u64 }) + (if e == 4u64 { 10000u64 } else { 0u64 }) + (if e == 5u64 { 100000u64 } else { 0u64 }) + (if e == 6u64 { 1000000u64 } else { 0u64 }) + (if e == 7u64 { 10000000u64 } else { 0u64 }) + (if e == 8u64 { 100000000u64 } else { 0u64 }) + (if e == 9u64 { 1000000000u64 } else { 0u64 }) + (if e == 10u64 { 10000000000u64 } else { 0u64 }) + (if e == 11u64 { 100000000000u64 } else { 0u64 }) + (if e == 12u64 { 1000000000000u64 } else { 0u64 }) + (if e == 13u64 { 10000000000000u64 } else { 0u64 }) + (if e == 14u64 { 100000000000000u64 } else { 0u64 }) + (if e == 15u64 { 1000000000000000u64 } else { 0u64 }) + (if e == 16u64 { 10000000000000000u64 } else { 0u64 }) + (if e == 17u64 { 100000000000000000u64 } else { 0u64 }) + (if e == 18u64 { 1000000000000000000u64 } else { 0u64 }) + (if e == 19u64 { 10000000000000000000u64 } else { 0u64 })
}
```

**Meaning:** `10` to the power `e` for `e < 20`, the exponents a 64-bit value's digits use.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::pow10(args))` when a proof needs the function body.

### `stdio::decimal_length`

```click
function decimal_length(v: uint64) -> uint64 {
    1u64 + (if v < 10u64 { 0u64 } else { 1u64 }) + (if v < 100u64 { 0u64 } else { 1u64 }) + (if v < 1000u64 { 0u64 } else { 1u64 }) + (if v < 10000u64 { 0u64 } else { 1u64 }) + (if v < 100000u64 { 0u64 } else { 1u64 }) + (if v < 1000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000000000u64 { 0u64 } else { 1u64 })
}
```

**Meaning:** The number of decimal digits `printf` writes for `v`: one for `v < 10`, so zero has one digit.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::decimal_length(args))` when a proof needs the function body.

### `stdio::decimal_digit`

```click
function decimal_digit(v: uint64, k: uint64) -> uint8 {
    if k < stdio::decimal_length(v) {
        (48u64 + v / stdio::pow10(stdio::decimal_length(v) - 1u64 - k) % 10u64) as uint8
    } else {
        48u8
    }
}
```

**Meaning:** The ASCII character of `v`'s `k`th decimal digit, counting from the most significant. Past the last digit, at `k >= stdio::decimal_length(v)`, it is `'0'` (`48u8`), so the function is total. Unfolding it owes nothing: specification `/` and `%` are total, so the digit's division by `stdio::pow10(...)` needs no nonzero premise.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::decimal_digit(args))` when a proof needs the function body.

### `stdio::padded_length`

```click
function padded_length(v: uint64, width: uint64) -> uint64 {
    if stdio::decimal_length(v) < width { width } else { stdio::decimal_length(v) }
}
```

**Meaning:** The characters `%Nu` writes for `v` in a field of width `N`: the field width, or `v`'s digits when they are wider.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::padded_length(args))` when a proof needs the function body.

### `stdio::padded_digit`

```click
function padded_digit(v: uint64, width: uint64, pad: uint8, k: uint64) -> uint8 {
    if to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)) {
        pad
    } else {
        stdio::decimal_digit(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v)))
    }
}
```

**Meaning:** The `k`th character of `v` in a field of `width`: `pad` (`'0'` for a `0` flag, `' '` otherwise) before the digits.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::padded_digit(args))` when a proof needs the function body.

### `stdio::magnitude`

```click
function magnitude(v: int32) -> uint64 {
    if v < 0 { (0i64 - v as int64) as uint64 } else { v as uint64 }
}
```

**Meaning:** The magnitude of an `int`, exact even for `INT_MIN`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::magnitude(args))` when a proof needs the function body.

### `stdio::signed_length`

```click
function signed_length(v: int32) -> uint64 {
    if v < 0 { 1u64 + stdio::decimal_length(stdio::magnitude(v)) } else { stdio::decimal_length(stdio::magnitude(v)) }
}
```

**Meaning:** The number of characters `%d` writes for `v`: its digits, after a `-` when it is negative.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::signed_length(args))` when a proof needs the function body.

### `stdio::signed_digit`

```click
function signed_digit(v: int32, k: uint64) -> uint8 {
    if v < 0 {
        if k == 0u64 { 45u8 } else { stdio::decimal_digit(stdio::magnitude(v), k - 1u64) }
    } else {
        stdio::decimal_digit(stdio::magnitude(v), k)
    }
}
```

**Meaning:** The `k`th character `%d` writes for `v`: a `-` first when it is negative, then the digits of its magnitude.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(stdio::signed_digit(args))` when a proof needs the function body.

### `stdio::pow10_0`

```click
theorem pow10_0() {
    ensures stdio::pow10(0u64) == 1u64 by {
        unfold(stdio::pow10(0u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `0`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_1`

```click
theorem pow10_1() {
    ensures stdio::pow10(1u64) == 10u64 by {
        unfold(stdio::pow10(1u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_2`

```click
theorem pow10_2() {
    ensures stdio::pow10(2u64) == 100u64 by {
        unfold(stdio::pow10(2u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `2`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_3`

```click
theorem pow10_3() {
    ensures stdio::pow10(3u64) == 1000u64 by {
        unfold(stdio::pow10(3u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `3`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_4`

```click
theorem pow10_4() {
    ensures stdio::pow10(4u64) == 10000u64 by {
        unfold(stdio::pow10(4u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `4`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_5`

```click
theorem pow10_5() {
    ensures stdio::pow10(5u64) == 100000u64 by {
        unfold(stdio::pow10(5u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `5`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_6`

```click
theorem pow10_6() {
    ensures stdio::pow10(6u64) == 1000000u64 by {
        unfold(stdio::pow10(6u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `6`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_7`

```click
theorem pow10_7() {
    ensures stdio::pow10(7u64) == 10000000u64 by {
        unfold(stdio::pow10(7u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `7`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_8`

```click
theorem pow10_8() {
    ensures stdio::pow10(8u64) == 100000000u64 by {
        unfold(stdio::pow10(8u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `8`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_9`

```click
theorem pow10_9() {
    ensures stdio::pow10(9u64) == 1000000000u64 by {
        unfold(stdio::pow10(9u64));
        close();
    }
}
```

**Meaning:** Evaluates `stdio::pow10` at `9`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::pow10_nonzero`

```click
theorem pow10_nonzero(e: uint64) {
    requires e < 20u64;
    ensures stdio::pow10(e) != 0u64 by {
        if e == 19u64 {
            unfold(stdio::pow10(e));
            close() using { e == 19u64; };
        } else {
            have e < 19u64 by { close() using { e < 20u64; not (e == 19u64); }; }
            if e == 18u64 {
                unfold(stdio::pow10(e));
                close() using { e == 18u64; };
            } else {
                have e < 18u64 by { close() using { e < 19u64; not (e == 18u64); }; }
                if e == 17u64 {
                    unfold(stdio::pow10(e));
                    close() using { e == 17u64; };
                } else {
                    have e < 17u64 by { close() using { e < 18u64; not (e == 17u64); }; }
                    if e == 16u64 {
                        unfold(stdio::pow10(e));
                        close() using { e == 16u64; };
                    } else {
                        have e < 16u64 by { close() using { e < 17u64; not (e == 16u64); }; }
                        if e == 15u64 {
                            unfold(stdio::pow10(e));
                            close() using { e == 15u64; };
                        } else {
                            have e < 15u64 by { close() using { e < 16u64; not (e == 15u64); }; }
                            if e == 14u64 {
                                unfold(stdio::pow10(e));
                                close() using { e == 14u64; };
                            } else {
                                have e < 14u64 by { close() using { e < 15u64; not (e == 14u64); }; }
                                if e == 13u64 {
                                    unfold(stdio::pow10(e));
                                    close() using { e == 13u64; };
                                } else {
                                    have e < 13u64 by { close() using { e < 14u64; not (e == 13u64); }; }
                                    if e == 12u64 {
                                        unfold(stdio::pow10(e));
                                        close() using { e == 12u64; };
                                    } else {
                                        have e < 12u64 by { close() using { e < 13u64; not (e == 12u64); }; }
                                        if e == 11u64 {
                                            unfold(stdio::pow10(e));
                                            close() using { e == 11u64; };
                                        } else {
                                            have e < 11u64 by { close() using { e < 12u64; not (e == 11u64); }; }
                                            if e == 10u64 {
                                                unfold(stdio::pow10(e));
                                                close() using { e == 10u64; };
                                            } else {
                                                have e < 10u64 by { close() using { e < 11u64; not (e == 10u64); }; }
                                                if e == 9u64 {
                                                    rewrite(e, 9u64);
                                                    apply(stdio::pow10_9());
                                                    rewrite(stdio::pow10(9u64), 1000000000u64);
                                                    close();
                                                } else {
                                                    have e < 9u64 by { close() using { e < 10u64; not (e == 9u64); }; }
                                                    if e == 8u64 {
                                                        rewrite(e, 8u64);
                                                        apply(stdio::pow10_8());
                                                        rewrite(stdio::pow10(8u64), 100000000u64);
                                                        close();
                                                    } else {
                                                        have e < 8u64 by { close() using { e < 9u64; not (e == 8u64); }; }
                                                        if e == 7u64 {
                                                            rewrite(e, 7u64);
                                                            apply(stdio::pow10_7());
                                                            rewrite(stdio::pow10(7u64), 10000000u64);
                                                            close();
                                                        } else {
                                                            have e < 7u64 by { close() using { e < 8u64; not (e == 7u64); }; }
                                                            if e == 6u64 {
                                                                rewrite(e, 6u64);
                                                                apply(stdio::pow10_6());
                                                                rewrite(stdio::pow10(6u64), 1000000u64);
                                                                close();
                                                            } else {
                                                                have e < 6u64 by { close() using { e < 7u64; not (e == 6u64); }; }
                                                                if e == 5u64 {
                                                                    rewrite(e, 5u64);
                                                                    apply(stdio::pow10_5());
                                                                    rewrite(stdio::pow10(5u64), 100000u64);
                                                                    close();
                                                                } else {
                                                                    have e < 5u64 by { close() using { e < 6u64; not (e == 5u64); }; }
                                                                    if e == 4u64 {
                                                                        rewrite(e, 4u64);
                                                                        apply(stdio::pow10_4());
                                                                        rewrite(stdio::pow10(4u64), 10000u64);
                                                                        close();
                                                                    } else {
                                                                        have e < 4u64 by { close() using { e < 5u64; not (e == 4u64); }; }
                                                                        if e == 3u64 {
                                                                            rewrite(e, 3u64);
                                                                            apply(stdio::pow10_3());
                                                                            rewrite(stdio::pow10(3u64), 1000u64);
                                                                            close();
                                                                        } else {
                                                                            have e < 3u64 by { close() using { e < 4u64; not (e == 3u64); }; }
                                                                            if e == 2u64 {
                                                                                rewrite(e, 2u64);
                                                                                apply(stdio::pow10_2());
                                                                                rewrite(stdio::pow10(2u64), 100u64);
                                                                                close();
                                                                            } else {
                                                                                have e < 2u64 by { close() using { e < 3u64; not (e == 2u64); }; }
                                                                                if e == 1u64 {
                                                                                    rewrite(e, 1u64);
                                                                                    apply(stdio::pow10_1());
                                                                                    rewrite(stdio::pow10(1u64), 10u64);
                                                                                    close();
                                                                                } else {
                                                                                    have e < 1u64 by { close() using { e < 2u64; not (e == 1u64); }; }
                                                                                    have e == 0u64 by { close() using { e < 1u64; }; }
                                                                                    rewrite(e, 0u64);
                                                                                    apply(stdio::pow10_0());
                                                                                    rewrite(stdio::pow10(0u64), 1u64);
                                                                                    close();
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
```

**Meaning:** Every exponent below 20, the exponents of a 64-bit value's digits, has a nonzero power of ten.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_1`

```click
theorem decimal_length_1(v: uint64) {
    requires v < 10u64;
    ensures stdio::decimal_length(v) == 1u64 by {
        have v < 10u64 by { close(); }
        have v < 100u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100u64)); }
        have v < 1000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000u64)); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10u64; }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100u64; }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 1 decimal digit has `stdio::decimal_length` 1.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_2`

```click
theorem decimal_length_2(v: uint64) {
    requires 10u64 <= v;
    requires v < 100u64;
    ensures stdio::decimal_length(v) == 2u64 by {
        have not (v < 10u64) by { close(); }
        have v < 100u64 by { close(); }
        have v < 1000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000u64)); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100u64; }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 2 decimal digits has `stdio::decimal_length` 2.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_3`

```click
theorem decimal_length_3(v: uint64) {
    requires 100u64 <= v;
    requires v < 1000u64;
    ensures stdio::decimal_length(v) == 3u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100u64, v)); }
        have not (v < 100u64) by { close(); }
        have v < 1000u64 by { close(); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 3 decimal digits has `stdio::decimal_length` 3.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_4`

```click
theorem decimal_length_4(v: uint64) {
    requires 1000u64 <= v;
    requires v < 10000u64;
    ensures stdio::decimal_length(v) == 4u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000u64, v)); }
        have not (v < 1000u64) by { close(); }
        have v < 10000u64 by { close(); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 4 decimal digits has `stdio::decimal_length` 4.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_5`

```click
theorem decimal_length_5(v: uint64) {
    requires 10000u64 <= v;
    requires v < 100000u64;
    ensures stdio::decimal_length(v) == 5u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 10000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 10000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 10000u64, v)); }
        have not (v < 10000u64) by { close(); }
        have v < 100000u64 by { close(); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 5 decimal digits has `stdio::decimal_length` 5.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_6`

```click
theorem decimal_length_6(v: uint64) {
    requires 100000u64 <= v;
    requires v < 1000000u64;
    ensures stdio::decimal_length(v) == 6u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 100000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 100000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 100000u64, v)); }
        have not (v < 100000u64) by { close(); }
        have v < 1000000u64 by { close(); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 6 decimal digits has `stdio::decimal_length` 6.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_7`

```click
theorem decimal_length_7(v: uint64) {
    requires 1000000u64 <= v;
    requires v < 10000000u64;
    ensures stdio::decimal_length(v) == 7u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 1000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 1000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 1000000u64, v)); }
        have not (v < 1000000u64) by { close(); }
        have v < 10000000u64 by { close(); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 7 decimal digits has `stdio::decimal_length` 7.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_8`

```click
theorem decimal_length_8(v: uint64) {
    requires 10000000u64 <= v;
    requires v < 100000000u64;
    ensures stdio::decimal_length(v) == 8u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 10000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 10000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 10000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 10000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 10000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 10000000u64, v)); }
        have not (v < 10000000u64) by { close(); }
        have v < 100000000u64 by { close(); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 8 decimal digits has `stdio::decimal_length` 8.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_9`

```click
theorem decimal_length_9(v: uint64) {
    requires 100000000u64 <= v;
    requires v < 1000000000u64;
    ensures stdio::decimal_length(v) == 9u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 100000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 100000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 100000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 100000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 100000000u64, v)); }
        have not (v < 10000000u64) by { apply(integer::uint64_less_equal_transitive(10000000u64, 100000000u64, v)); }
        have not (v < 100000000u64) by { close(); }
        have v < 1000000000u64 by { close(); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100000000u64); }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 9 decimal digits has `stdio::decimal_length` 9.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_length_10`

```click
theorem decimal_length_10(v: uint64) {
    requires 1000000000u64 <= v;
    requires v < 10000000000u64;
    ensures stdio::decimal_length(v) == 10u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 1000000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 1000000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 1000000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 1000000000u64, v)); }
        have not (v < 10000000u64) by { apply(integer::uint64_less_equal_transitive(10000000u64, 1000000000u64, v)); }
        have not (v < 100000000u64) by { apply(integer::uint64_less_equal_transitive(100000000u64, 1000000000u64, v)); }
        have not (v < 1000000000u64) by { close(); }
        have v < 10000000000u64 by { close(); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 100000000u64); }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 1u64 by { close() using { not (v < 1000000000u64); }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { close() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        close();
    }
}
```

**Meaning:** A value with 10 decimal digits has `stdio::decimal_length` 10.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_digit_power_nonzero`

```click
theorem decimal_digit_power_nonzero(v: uint64, k: uint64) {
    requires k < stdio::decimal_length(v);
    ensures stdio::pow10(stdio::decimal_length(v) - 1u64 - k) != 0u64 by {
        have stdio::decimal_length(v) <= 20u64 by {
            unfold(stdio::decimal_length(v));
            close();
        }
        have (stdio::decimal_length(v) - 1u64 - k) as uint64 < 20u64 by { close(); }
        apply(stdio::pow10_nonzero(stdio::decimal_length(v) - 1u64 - k));
    }
}
```

**Meaning:** Where `k` names one of `v`'s digits, the power of ten that selects it is nonzero, so the digit's division by it is an ordinary quotient rather than the opaque quotient by zero.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_digit_of_length`

```click
theorem decimal_digit_of_length(v: uint64, n: uint64, k: uint64) {
    requires stdio::decimal_length(v) == n;
    requires k < n;
    ensures stdio::decimal_digit(v, k) == (48u64 + v / stdio::pow10(n - 1u64 - k) % 10u64) as uint8 by {
        unfold(stdio::decimal_digit(v, k));
        rewrite(stdio::decimal_length(v), n);
        close() using { k < n; };
    }
}
```

**Meaning:** Rewrites digit `k < n` of a value whose length is known to be `n` to `48 + v / 10^(n-1-k) % 10`. For known `n` and `k`, `stdio::pow10_e` gives the value of the power `stdio::pow10(n - 1u64 - k)` it divides by.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::decimal_digit_lower_bound`

```click
theorem decimal_digit_lower_bound(v: uint64, k: uint64) {
    ensures 48u8 <= stdio::decimal_digit(v, k) by {
        if k < stdio::decimal_length(v) {
            apply(stdio::decimal_digit_power_nonzero(v, k));
            apply(stdio::decimal_digit_of_length(v, stdio::decimal_length(v), k));
            rewrite(stdio::decimal_digit(v, k), (48u64 + v / stdio::pow10(stdio::decimal_length(v) - 1u64 - k) % 10u64) as uint8);
            close();
        } else {
            unfold(stdio::decimal_digit(v, k));
            close() using { not (k < stdio::decimal_length(v)); };
        }
    }
}
```

**Meaning:** Every decimal digit is a character from `'0'` up, so none is the terminator `0`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `stdio::padded_digit_lower_bound`

```click
theorem padded_digit_lower_bound(v: uint64, width: uint64, k: uint64) {
    ensures 48u8 <= stdio::padded_digit(v, width, 48u8, k) by {
        unfold(stdio::padded_digit(v, width, 48u8, k));
        if to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)) {
            have (if to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)) { 48u8 } else { stdio::decimal_digit(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))) }) == 48u8 by {
                close() using { to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)); };
            }
            rewrite((if to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)) { 48u8 } else { stdio::decimal_digit(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))) }), 48u8);
            close();
        } else {
            apply(stdio::decimal_digit_lower_bound(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))));
            close() using { not (to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v))); 48u8 <= stdio::decimal_digit(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))); };
        }
    }
}
```

**Meaning:** Every character of a `0`-padded field is a digit or the `'0'` pad, so none is the terminator; this is what a `%s` of a `%03u` fraction needs.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## `click::c::string`

`library/c/string.interface.click` defines the C library contracts and the proof
vocabulary for C strings. A C declaration or call brings the modeled
contracts. To use a proof helper, a sidecar can name its full path or import
the module. For example, `import click::c::string::{cstr_at, readable};`
selects the C-string resource and its readability predicate.

### External C contracts

These declarations cover the narrow byte-oriented libc slice supported by Click.
They are body-less assumptions: callers must satisfy their requirements, and
Click does not verify an implementation of the external function.

### `fprintf`

```click
int32 fprintf(FILE* file, const uint8* format, ...args) {
    let n: uint64;
    views click::c::string::cstr_at(format, n);
    requires n <= 2147483647u64;
    requires click::c::stdio::literal_format(format, 0u64, n as int32);
    owns out: click::c::stdio::stream(file);
    ensures result == click::c::stdio::format_length(format, 0u64, n as int32, 0) or result < 0;
    ensures out.write_history == List::Cons(
        WriteAttempt::Attempt(click::c::stdio::format_output(format, 0u64, n as int32), result),
        old(out.write_history));
    ensures click::c::stdio::write_requests(out.write_history) == List::Cons(
        click::c::stdio::format_output(format, 0u64, n as int32),
        old(click::c::stdio::write_requests(out.write_history)));
}
```

**Meaning:** Writes the characters a format of ordinary characters and `%%`
produces to the stream `file` and adds the attempt to the front of its
history: the count on success, or a negative value on an error, which may
follow partial output. The format is a C string the caller views, and its
arguments, which such a format does not convert, are ignored. The C front end
selects this contract for the projected `<stdio.h>` declaration
([formatted output](../language/c.md#formatted-output)).

**Verified use:** [`mdtests/printf_and_fprintf_share_the_streams_write_history.md`](https://github.com/clicklang/click/blob/master/mdtests/printf_and_fprintf_share_the_streams_write_history.md); a format that converts is refused in [`mdtests/fprintf_refuses_a_format_that_converts.md`](https://github.com/clicklang/click/blob/master/mdtests/fprintf_refuses_a_format_that_converts.md).

### `printf`

```click
int32 printf(const uint8* format, ...args) {
    let n: uint64;
    views click::c::string::cstr_at(format, n);
    requires n <= 2147483647u64;
    requires click::c::stdio::literal_format(format, 0u64, n as int32);
    owns out: click::c::stdio::stream(stdout);
    ensures result == click::c::stdio::format_length(format, 0u64, n as int32, 0) or result < 0;
    ensures out.write_history == List::Cons(
        WriteAttempt::Attempt(click::c::stdio::format_output(format, 0u64, n as int32), result),
        old(out.write_history));
    ensures click::c::stdio::write_requests(out.write_history) == List::Cons(
        click::c::stdio::format_output(format, 0u64, n as int32),
        old(click::c::stdio::write_requests(out.write_history)));
}
```

**Meaning:** [`fprintf`](#fprintf) with the stream `stdout`, the hosted
target's standard output, which the contract names as a program global. The
C front end selects this contract for the projected `<stdio.h>` declaration
on the hosted target ([formatted output](../language/c.md#formatted-output)).

**Verified use:** [`mdtests/printf_and_fprintf_share_the_streams_write_history.md`](https://github.com/clicklang/click/blob/master/mdtests/printf_and_fprintf_share_the_streams_write_history.md); a format that converts is refused in [`mdtests/printf_refuses_a_format_that_converts.md`](https://github.com/clicklang/click/blob/master/mdtests/printf_refuses_a_format_that_converts.md).

### `memcpy`

```click
uint8* memcpy(uint8 destination[], const uint8 source[], uint64 bytes) {
    views source[0..bytes];
    owns uninitialized(destination[0..bytes]);
    ensures result == destination;
    ensures bytes::equal(destination, 0u64, old(source), 0u64, bytes);
}
```

**Meaning:** Copies `bytes` bytes, a `size_t` count as in C, from a viewed source to
an owned destination and returns the destination pointer. The caller lends
the source for the call from bytes it views or owns. The `owns` and `views`
clauses of one contract are disjoint, so a call whose source overlaps its
destination is refused
([`mdtests/byte_representation_overlapping_copy_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/byte_representation_overlapping_copy_rejected.md)),
and `viewable` alone, which grants no read authority, does not lend the
source
([`mdtests/memcpy_source_needs_a_covering_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/memcpy_source_needs_a_covering_resource.md)). This exact
standard-library declaration also carries the checked representation-copy
effect: after the call, each initialized typed cell whose complete byte
representation lies in the copied range is established at the mapped
destination offset. A source cell the copy would split, a symbolic range, an
unaligned destination, and an untyped source establish no typed value. The
effect is bound to this declaration, not to the name `memcpy`.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/byte_representation_scalar_copy.md`](https://github.com/clicklang/click/blob/master/mdtests/byte_representation_scalar_copy.md) checks its typed-copy effect, and [`mdtests/memcpy_reads_a_viewed_or_borrowed_source.md`](https://github.com/clicklang/click/blob/master/mdtests/memcpy_reads_a_viewed_or_borrowed_source.md) copies from a viewed source and from an owned one lent for the call.

### `memcmp`

```click
int32 memcmp(const uint8 left[], const uint8 right[], uint64 bytes) {
    views left[0..bytes];
    views right[0..bytes];
    requires forall (k: uint64) { k < bytes implies defined(left[k]) and defined(right[k]) };
    ensures bytes::comparison(left, right, bytes, result);
}
```

**Meaning:** Reads both `bytes`-long byte ranges (a `size_t` count, as in C) under views, without mutation. Equal ranges yield zero. For unequal ranges, the first differing byte determines the sign, with both bytes interpreted as unsigned: smaller left means negative and larger left means positive. No exact magnitude is promised. Views are shared, so one viewed or owned range can be both operands. The zero-count case yields zero. The external contract is an assumption about the C library; the `bytes::comparison_*` theorems are checked consequences of its comparison relation.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](https://github.com/clicklang/click/blob/master/mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md) checks its range and definedness preconditions at a call, and [`mdtests/memcmp_reads_two_viewed_buffers.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_reads_two_viewed_buffers.md) compares two viewed buffers and one buffer with itself. Ordering, equal prefixes, unsigned high bytes, and the equal/empty cases are checked in `mdtests/memcmp_orders_the_first_differing_byte.md`, `mdtests/memcmp_orders_after_equal_prefix.md`, `mdtests/memcmp_orders_high_unsigned_bytes.md`, `mdtests/memcmp_equal_bytes_compare_as_zero.md`, and `mdtests/memcmp_zero_bytes_compare_as_zero.md`. Negative controls reject a wrong sign, a later difference overriding the first, an exact-magnitude claim, and uninitialized inputs.

### `memset`

```click
uint8* memset(uint8 destination[], int32 value, uint64 bytes) {
    owns uninitialized(destination[0..bytes]);
    ensures result == destination;
    ensures (0u64..bytes).all(|k| {
        defined(destination[k]) and destination[k] == (value as uint8)
    });
}
```

**Meaning:** Fills `bytes` bytes (a `size_t` count, as in C) of an owned
destination with `value` converted to `unsigned char`, and returns the
destination pointer. Every `int32` fill value is accepted. Conversion reduces
it modulo 256: `-1` fills with 255 and `300` fills with 44.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/memset_converts_fill_value_to_unsigned_char.md`](https://github.com/clicklang/click/blob/master/mdtests/memset_converts_fill_value_to_unsigned_char.md) checks negative, large and symbolic fill values over a symbolic length. [`mdtests/c_builtin_memset_header_checks_its_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/c_builtin_memset_header_checks_its_contract.md) checks the built-in header's binding to this contract.

### `strlen`

```click
uint64 strlen(const uint8* bytes) {
    let n: uint64;
    views cstr_at(bytes, n);
    ensures result == n;
}
```

**Meaning:** Returns the `size_t` length of the C string `cstr_at(bytes, n)`
the caller holds, without mutation, as C's `strlen` does. The value
parameter `n` is the length, which the C signature does not carry. A call
takes it from the one held `cstr_at` at `bytes` (`views`, `owns`, or an
owner lending it), or from a call map, `{ n: k }`, whose string the call
assembles from owned bytes and the string's facts when the caller holds
none. The string's facts (the length is
below `SIZE_MAX`, no earlier terminator, the terminator at `len`, every byte
defined) come with the instance, so the result points at its terminator.
`string::readable` alone grants no resource and does not satisfy the call.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](https://github.com/clicklang/click/blob/master/mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md) returns zero for `cstr_at(text, 0u64)`;
[`mdtests/cstr_readable_witness_stated_before_call.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_readable_witness_stated_before_call.md)
names the string a call assembles; and
[`mdtests/cstr_dynamic_indexed_read_requires_permission.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_dynamic_indexed_read_requires_permission.md)
refuses a caller that holds only `string::readable`.

### C-string resources, predicates and theorems

### `string::prefix`

```click
predicate prefix(bytes: uint8[], len: uint64) {
    forall (k: uint64) { k < len implies bytes[k] != '\0' }
}
```

**Meaning:** States that the first `len` bytes contain no null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(string::prefix(args))` when a proof needs the predicate body.

### `string::len`

```click
predicate len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        string::prefix(bytes, len) and
        bytes[len] == '\0'
}
```

**Meaning:** States that `len` is a `size_t` length below `SIZE_MAX`, the
complete prefix through its terminator is readable, the preceding bytes contain
no null terminator, and byte `len` is a null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(string::len(args))` when a proof needs the predicate body.

### `string::cstr`

```click
predicate cstr(bytes: uint8[]) {
    exists (len: uint64) {
        string::len(bytes, len)
    }
}
```

**Meaning:** States that the byte array has some exact specification-level C-string length.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(string::cstr(args))` when a proof needs the predicate body.

### `string::readable_len`

```click
predicate readable_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        forall (k: uint64) { k < len implies bytes[k] != '\0' } and
        bytes[len] == '\0' and
        forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
}
```

**Meaning:** States that `len` is a `size_t` C-string length below
`SIZE_MAX`, the complete prefix through its terminator is dynamically viewable,
the prefix has no embedded terminator, and every byte through the null
terminator is defined.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(string::readable_len(args))` when a proof needs the predicate body.

### `string::readable_len_unique`

```click
theorem readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) { k < left implies bytes[k] != '\0' };
    requires bytes[left] == '\0';
    requires forall (k: uint64) { k < right implies bytes[k] != '\0' };
    requires bytes[right] == '\0';

    ensures left == right by {
        have left < right or not (left < right) by {
            if left < right {
                close();
            } else {
                close();
            }
        }
        cases {
            left < right => {
                instantiate(forall (k: uint64) { k < right implies bytes[k] != '\0' }, left);
                contradiction();
            }
            not (left < right) => {
                have right < left or not (right < left) by {
                    if right < left {
                        close();
                    } else {
                        close();
                    }
                }
                cases {
                    right < left => {
                        instantiate(forall (k: uint64) { k < left implies bytes[k] != '\0' }, right);
                        contradiction();
                    }
                    not (right < left) => {
                        have to_integer(left) <= to_integer(right) by close();
                        have to_integer(right) <= to_integer(left) by close();
                        apply(integer::le_antisymmetric(to_integer(left), to_integer(right)));
                        close();
                    }
                }
            }
        }
    }
}
```

**Meaning:** Proves that two `size_t` lengths with the same null-free prefix
condition and null terminator for one byte array are equal. It is a pure
content theorem; it does not grant viewability or read/write permission.

**Kind:** theorem. The proof is checked as part of the standard-library
definition and its requirements and guarantee are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `string::readable`

```click
predicate readable(bytes: uint8[]) {
    exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
    }
}
```

**Meaning:** States that the byte array has some dynamically viewable,
null-terminated C-string prefix. The length remains existential; unfold the
predicate when a proof needs to expose that witness. A caller can pass the same
unchanged plain-`char` or signed-character pointer to a callee requiring this predicate:
contract expansion retains the predicate's unsigned byte reads. The caller
must supply the requirement; it does not cover an offset pointer or survive
an arbitrary write to the string. See
[`cstr_plain_char_caller_requirement_reaches_callee.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_plain_char_caller_requirement_reaches_callee.md).

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(string::readable(args))` when a proof needs the predicate body.

### `cstr_at`

```click
resource cstr_at(p: const uint8*, len: uint64) {
    owns p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(len + 1u64) implies defined(p[k]) };
}
```

**Meaning:** A C string: the `len + 1` bytes of `p` through its first
terminator, with the facts that make them the C string of length `len`. The
body owns the bytes, and a contract chooses how it holds them. `views
cstr_at(p, len);` borrows the string read-only: the callee cannot write it,
and an opened view exposes the bytes as views. `owns cstr_at(p, len);` holds
it exclusively and returns the same instance, so `len` is unchanged at exit.
A function that changes the length, such as one that writes an earlier
terminator, states `consumes cstr_at(p, len);` and `produces` the new
instance with the bytes it no longer covers. The bytes determine `len`, so
`fold(cstr_at(p, m))` at any other length fails. An owner lends its instance
to a callee that views it, and a caller that owns the bytes and holds the
facts but no instance has the call assemble the view; the caller keeps its
bytes. `with(cstr_at(p, len)) { ... }` exposes the body and the facts. A
`char`, `signed char`, or `unsigned char` pointer may be passed for `p`, as
for the C-string predicates; a signed character pointer is read through its
byte view `p as (uint8 *)`.

**Kind:** composite resource. Parameter types, memory clause, and facts are normative in the declaration above.

**Verified use:** [`cstr_at_view_passes_through_a_call.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_view_passes_through_a_call.md),
[`cstr_at_opens_and_lends_a_prefix_to_a_copy.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_opens_and_lends_a_prefix_to_a_copy.md),
[`cstr_at_fold_refuses_a_wrong_length.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_fold_refuses_a_wrong_length.md),
[`cstr_at_viewed_string_cannot_be_written.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_viewed_string_cannot_be_written.md),
[`cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md),
[`cstr_at_owns_clause_cannot_shorten_the_string.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_owns_clause_cannot_shorten_the_string.md),
[`cstr_at_consumes_and_produces_a_shorter_string.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_consumes_and_produces_a_shorter_string.md),
[`cstr_at_owner_lends_its_string_to_a_viewing_callee.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_owner_lends_its_string_to_a_viewing_callee.md),
[`cstr_at_call_assembles_a_view_from_owned_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_call_assembles_a_view_from_owned_bytes.md),
and, through character pointers,
[`cstr_at_borrows_a_char_string_from_the_library.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_borrows_a_char_string_from_the_library.md).

### `string::bounded`

```click
predicate bounded(bytes: uint8[], max: uint64) {
    exists (k: uint64) { k < max and bytes[k] == '\0' }
}
```

**Meaning:** States that a null terminator occurs before the exclusive bound `max`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(string::bounded(args))` when a proof needs the predicate body.

### `string::len_is_viewable`

```click
theorem len_is_viewable(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        unfold(string::len(bytes, len));
        close();
    }
}
```

**Meaning:** Given an exact C-string length, exposes the viewability of the
prefix and its terminator as a separate fact for a subsequent proof step.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/cstr_viewable_witness.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_viewable_witness.md) checks this witness projection.

### `string::len_has_prefix`

```click
theorem len_has_prefix(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures string::prefix(bytes, len) by {
        unfold(string::len(bytes, len));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `string::prefix(bytes, len)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `string::len_has_terminator`

```click
theorem len_has_terminator(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures bytes[len] == '\0' by {
        unfold(string::len(bytes, len));
        close();
    }
}
```

**Meaning:** Given its listed requirements, proves `bytes[len] == '\0'`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## C++ standard library interfaces

Source: `library/cpp/span.interface.click`, `library/cpp/array.interface.click` and
`library/cpp/as_writable_bytes.interface.click`. These files are not modules: the C++
importer adds the selected contracts to the sidecar's environment and writes each
`template<...> extern` block out at each element type and extent a call
names, `std::span<int>::size`. Its name table,
`src/languages/cpp/standard_library.rs`, lists the functions and element
types it maps to them. The model accessors `std_span_data`,
`std_span_size` and `std_array_data` name a span's or array's state.

### C++ `memcpy`

The C++ interface uses the native pointer types and the same byte equality
predicate as the C interface. It borrows initialized source bytes and
turns writable destination storage into an initialized byte range.

```click
void* memcpy(void* destination, const void* source, unsigned long bytes) {
    views (source as (const uint8*))[0..bytes];
    consumes uninitialized((destination as (uint8*))[0..bytes]);
    produces (destination as (uint8*))[0..bytes];
    ensures result == destination;
    ensures bytes::equal(destination as (uint8*), 0u64, old(source as (const uint8*)), 0u64, bytes);
}
```

**Verified use:** [C++ importer tests](https://github.com/clicklang/click/blob/master/tests/cpp_import.rs)
copy a byte through the implicit pointer conversions and check the required
destination authority.

### `std::vector<unsigned char>`

The `click::cpp::vector_state::vector_state` resource records an existing
byte vector's length and backing address. `size()`, `empty()`, and
`data()` preserve it. Const `operator[]` preserves it too and returns a
reference at the given byte offset when the index is less than the length.
A caller that reads through the reference needs authority
over the initialized byte range. The pinned libstdc++ fixture declares a
byte-range resource in the sidecar, holds it alongside `vector_state(&bytes)`,
and relates their `data` and `length` fields in the caller's contract. It
unfolds the byte resource before passing the span to a reader and folds it
again afterward.

**Verified use:** [C++ importer tests](https://github.com/clicklang/click/blob/master/tests/cpp_import.rs)
check the catalog calls. The [pinned libstdc++ tests](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs)
pass a byte vector's backing storage to a span reader and read directly
through a bounded vector subscript.

```click
abstract resource vector_state(vector: const void*) {
    field length: uint64;
    field data: uint8*;
}

unsigned long std::vector<unsigned char>::size() const {
    owns state: vector_state(this);
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures result == state.length;
}

bool std::vector<unsigned char>::empty() const {
    owns state: vector_state(this);
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures state.length == 0u64 implies result;
    ensures state.length != 0u64 implies not result;
}

const unsigned char* std::vector<unsigned char>::data() const {
    owns state: vector_state(this);
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures result == state.data;
}

const unsigned char& std::vector<unsigned char>::operator[](unsigned long index) const {
    owns state: vector_state(this);
    requires index < state.length;
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures &result == state.data + index;
}
```

### `std::span<T>`

The catalog also supplies copy construction and `empty()` for dynamic
`std::span<int>`. These use the logical descriptor resource
`click::cpp::span_state::span_state`, defined in `library/cpp/span_state.click`.
Copy construction produces a new descriptor resource with the same address
and count while preserving the source. `empty()` observes the count and
preserves the descriptor. The resource grants no access to backing memory.

```click
abstract resource span_state(span: uint8*) {
    field data: int32*;
    field count: uint64;
}

template<class T> std::span<T>::span(const std::span<T>& source) {
    owns input: span_state(&source as (uint8*));
    produces copy: span_state(this as (uint8*));
    ensures input.data == old(input.data);
    ensures input.count == old(input.count);
    ensures copy.data == input.data;
    ensures copy.count == input.count;
}

template<class T> bool std::span<T>::empty() const {
    owns state: span_state(this as (uint8*));
    ensures state.data == old(state.data);
    ensures state.count == old(state.count);
    ensures state.count == 0u64 implies result;
    ensures state.count != 0u64 implies not result;
}
```


The dynamic pointer/count constructor initializes the descriptor and establishes
its address and count. Its contract grants no authority over the backing.

```click
template<class T> std::span<T>::span<T *>(T* first, unsigned long count) {
    consumes uninitialized(this[0..1]);
    produces this[0..1];
    ensures std_span_data(this) == first;
    ensures std_span_size(this) == count;
}
template<class T> unsigned long std::span<T>::size() const {
    views std_span_size(this);
    ensures result == std_span_size(this);
}
template<class T> unsigned long std::span<T>::size_bytes() const {
    views std_span_size(this);
    ensures result == std_span_size(this) * sizeof(T);
}
template<class T> T* std::span<T>::data() const {
    views std_span_data(this);
    ensures result == std_span_data(this);
}
template<class T> T& std::span<T>::front() const {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this);
}
template<class T> T& std::span<T>::back() const {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this) + (std_span_size(this) - 1u64);
}
template<class T> T& std::span<T>::operator[](unsigned long index) const {
    views std_span_data(this);
    views std_span_size(this);
    requires index < std_span_size(this);
    ensures &result == std_span_data(this) + index;
}
template<class T> std::span<T> std::span<T>::first(unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires count <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == count;
}
template<class T> std::span<T> std::span<T>::last(unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires count <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this) + (std_span_size(this) - count);
    ensures std_span_size(result) == count;
}
template<class T> std::span<T> std::span<T>::subspan(unsigned long offset, unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires offset <= std_span_size(this);
    requires count != 18446744073709551615u64 implies count <= std_span_size(this) - offset;
    ensures std_span_data(result) == std_span_data(this) + offset;
    ensures count == 18446744073709551615u64 implies std_span_size(result) == std_span_size(this) - offset;
    ensures count != 18446744073709551615u64 implies std_span_size(result) == count;
}
```

**Meaning:** A dynamic-extent span is a view of `[data, data + size)`. The
element accessors require an index inside the view and form an address
without reading it; the subviews require the subview to lie inside the view
and keep the backing storage. `subspan`'s count `std::dynamic_extent`,
`18446744073709551615u64`, means "to the end".

**Kind:** C++ standard library interface. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) calls each through `axiomatic_span_*` probes, and refuses each requirement it drops (nightly).

### `std::span<T, N>`

```click
template<class T, std::size_t N> unsigned long std::span<T, N>::size() const {
    ensures result == N;
}
template<class T, std::size_t N> unsigned long std::span<T, N>::size_bytes() const {
    ensures result == N * sizeof(T);
}
template<class T, std::size_t N> T* std::span<T, N>::data() const {
    views std_span_data(this);
    ensures result == std_span_data(this);
}
template<class T, std::size_t N> T& std::span<T, N>::front() const {
    views std_span_data(this);
    requires 1u64 <= N;
    ensures &result == std_span_data(this);
}
template<class T, std::size_t N> T& std::span<T, N>::back() const {
    views std_span_data(this);
    requires 1u64 <= N;
    ensures &result == std_span_data(this) + (N - 1u64);
}
template<class T, std::size_t N> T& std::span<T, N>::operator[](unsigned long index) const {
    views std_span_data(this);
    requires index < N;
    ensures &result == std_span_data(this) + index;
}
template<class T, std::size_t N> std::span<T> std::span<T, N>::first(unsigned long count) const {
    views std_span_data(this);
    requires count <= N;
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == count;
}
template<class T, std::size_t N> std::span<T> std::span<T, N>::last(unsigned long count) const {
    views std_span_data(this);
    requires count <= N;
    ensures std_span_data(result) == std_span_data(this) + (N - count);
    ensures std_span_size(result) == count;
}
template<class T, std::size_t N> std::span<T> std::span<T, N>::subspan(unsigned long offset, unsigned long count) const {
    views std_span_data(this);
    requires offset <= N;
    requires count != 18446744073709551615u64 implies count <= N - offset;
    ensures std_span_data(result) == std_span_data(this) + offset;
    ensures count == 18446744073709551615u64 implies std_span_size(result) == N - offset;
    ensures count != 18446744073709551615u64 implies std_span_size(result) == count;
}
```

**Meaning:** A static-extent span is a view of `[data, data + N)`. `N` is
the template argument, written at an instance as a literal, `4u64`; only the
data pointer is state. The subviews taking a runtime count are
dynamic-extent spans.

**Kind:** C++ standard library interface. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) reads, measures and subviews `std::span<int, 4>` and `std::span<const unsigned char, 32>` in `axiomatic_static_extent_*` (nightly).

### `std::array<T, N>`

```click
template<class T, std::size_t N> unsigned long std::array<T, N>::size() const {
    ensures result == N;
}
template<class T, std::size_t N> T* std::array<T, N>::data() {
    ensures result == &std_array_data(this)[0];
}
template<class T, std::size_t N> const T* std::array<T, N>::data() const {
    ensures result == &std_array_data(this)[0];
}
template<class T, std::size_t N> T& std::array<T, N>::operator[](unsigned long index) {
    requires index < N;
    ensures &result == &std_array_data(this)[index];
}
template<class T, std::size_t N> const T& std::array<T, N>::operator[](unsigned long index) const {
    requires index < N;
    ensures &result == &std_array_data(this)[index];
}
template<class T, std::size_t N> T& std::array<T, N>::front() {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[0];
}
template<class T, std::size_t N> const T& std::array<T, N>::front() const {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[0];
}
template<class T, std::size_t N> T& std::array<T, N>::back() {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[N - 1u64];
}
template<class T, std::size_t N> const T& std::array<T, N>::back() const {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[N - 1u64];
}
```

**Meaning:** A `std::array<T, N>` holds `N` elements in the object, named by
`std_array_data(a)`. Each accessor has a `const` and a mutable overload,
written as its own template; an instance is written from the overload whose
receiver constness it has. The element accessors require an index inside
the array and form an address without reading it.

**Kind:** C++ standard library interface. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) reads and writes elements in `axiomatic_std_array_reference_element_resources_verify`, and calls `size`, `data` and `back` in the nightly `axiomatic_std_array_*` tests.

### `std::as_writable_bytes<T, N>`

```click
template<class T, std::size_t N> std::span<std::byte> std::as_writable_bytes<T, N>(std::span<T> s) {
    ensures std_span_data(result) == old(std_span_data(s) as (uint8 *));
    ensures std_span_size(result) == old(std_span_size(s)) * sizeof(T);
}
```

**Meaning:** The same storage as a span of bytes: the backing address as
`uint8 *` and `sizeof(T)` bytes per element. It reads and grants nothing.
The argument is a span passed by value, so the result is stated from it as
it was on entry.

**Kind:** C++ standard library interface. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) views an `std::span<int>` as bytes in `pinned_writable_byte_span_*` (nightly).

## `click::rust::i8` through `click::rust::usize`

Source: `library/rust/i8.click` through `library/rust/usize.click`, one module per Rust integer type, imported as `import click::rust::u32;`. The Rust integer-method contracts of `library/rust/integers.interface.click` name them by path.

### Rust core methods

`click::rust::i8` through `click::rust::usize` define, for each Rust integer
type, the core methods the Rust importer specifies: `min`, `max`,
`wrapping_add`, `wrapping_sub`, `wrapping_mul`, `saturating_add`,
`saturating_sub`, `checked_add`, `checked_sub`, `abs_diff`, and, for a signed
type, `unsigned_abs`. A call of one of these methods in imported Rust calls an
external function whose contract is the library's
([Rust integer methods](#rust-integer-methods)), `ensures result ==
click::rust::u32::min(a, b);`, so a sidecar states and proves claims about it
with the same function after `import click::rust::u32;`. Each is opaque until
`unfold` gives its definition. A signed type's wrapping arithmetic, `abs_diff`
and `unsigned_abs` go through the unsigned type of its width, whose casts are
modular; an 8- or 16-bit result is cast back from C's promoted `int`.

### Rust names for library lemmas

A Rust proof applies the library lemmas it needs by Rust names, in the
module of the operand type: `u32::multiply_to_integer`,
`usize::multiply_to_integer` and `usize::product_bound_from_division`. Each
restates a width-named lemma of [`click::integer`](#clickinteger) and is
proved by applying it, so it adds no trust. These modules import
`click::integer` for those proofs; a sidecar that applies a Rust name needs
only `import click::rust::u32;` or `import click::rust::usize;`.

### `i8::min`

```click
function min(a: int8, b: int8) -> int8 {
    if a <= b { a } else { b }
}
```

### `i8::max`

```click
function max(a: int8, b: int8) -> int8 {
    if a <= b { b } else { a }
}
```

### `i8::wrapping_add`

```click
function wrapping_add(a: int8, b: int8) -> int8 {
    a + b
}
```

### `i8::wrapping_sub`

```click
function wrapping_sub(a: int8, b: int8) -> int8 {
    a - b
}
```

### `i8::wrapping_mul`

```click
function wrapping_mul(a: int8, b: int8) -> int8 {
    a * b
}
```

### `i8::saturating_add`

```click
function saturating_add(a: int8, b: int8) -> int8 {
    if to_integer(a) + to_integer(b) > 127 {
        (127i64 as int8)
    } else {
        if to_integer(a) + to_integer(b) < -128 {
            (-128i64 as int8)
        } else {
            ((a as uint8) + (b as uint8)) as int8
        }
    }
}
```

### `i8::saturating_sub`

```click
function saturating_sub(a: int8, b: int8) -> int8 {
    if to_integer(a) - to_integer(b) > 127 {
        (127i64 as int8)
    } else {
        if to_integer(a) - to_integer(b) < -128 {
            (-128i64 as int8)
        } else {
            ((a as uint8) - (b as uint8)) as int8
        }
    }
}
```

### `i8::checked_add`

```click
function checked_add(a: int8, b: int8) -> Option<int8> {
    if -128 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 127 {
        Option<int8>::Some(((a as uint8) + (b as uint8)) as int8)
    } else {
        Option<int8>::None
    }
}
```

### `i8::checked_sub`

```click
function checked_sub(a: int8, b: int8) -> Option<int8> {
    if -128 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 127 {
        Option<int8>::Some(((a as uint8) - (b as uint8)) as int8)
    } else {
        Option<int8>::None
    }
}
```

### `i8::abs_diff`

```click
function abs_diff(a: int8, b: int8) -> uint8 {
    if b <= a { ((a as uint8) - (b as uint8)) as uint8 } else { ((b as uint8) - (a as uint8)) as uint8 }
}
```

### `i8::unsigned_abs`

```click
function unsigned_abs(a: int8) -> uint8 {
    if a < (0i64 as int8) { ((0u32 as uint8) - (a as uint8)) as uint8 } else { a as uint8 }
}
```

### `i16::min`

```click
function min(a: int16, b: int16) -> int16 {
    if a <= b { a } else { b }
}
```

### `i16::max`

```click
function max(a: int16, b: int16) -> int16 {
    if a <= b { b } else { a }
}
```

### `i16::wrapping_add`

```click
function wrapping_add(a: int16, b: int16) -> int16 {
    a + b
}
```

### `i16::wrapping_sub`

```click
function wrapping_sub(a: int16, b: int16) -> int16 {
    a - b
}
```

### `i16::wrapping_mul`

```click
function wrapping_mul(a: int16, b: int16) -> int16 {
    a * b
}
```

### `i16::saturating_add`

```click
function saturating_add(a: int16, b: int16) -> int16 {
    if to_integer(a) + to_integer(b) > 32767 {
        (32767i64 as int16)
    } else {
        if to_integer(a) + to_integer(b) < -32768 {
            (-32768i64 as int16)
        } else {
            ((a as uint16) + (b as uint16)) as int16
        }
    }
}
```

### `i16::saturating_sub`

```click
function saturating_sub(a: int16, b: int16) -> int16 {
    if to_integer(a) - to_integer(b) > 32767 {
        (32767i64 as int16)
    } else {
        if to_integer(a) - to_integer(b) < -32768 {
            (-32768i64 as int16)
        } else {
            ((a as uint16) - (b as uint16)) as int16
        }
    }
}
```

### `i16::checked_add`

```click
function checked_add(a: int16, b: int16) -> Option<int16> {
    if -32768 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 32767 {
        Option<int16>::Some(((a as uint16) + (b as uint16)) as int16)
    } else {
        Option<int16>::None
    }
}
```

### `i16::checked_sub`

```click
function checked_sub(a: int16, b: int16) -> Option<int16> {
    if -32768 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 32767 {
        Option<int16>::Some(((a as uint16) - (b as uint16)) as int16)
    } else {
        Option<int16>::None
    }
}
```

### `i16::abs_diff`

```click
function abs_diff(a: int16, b: int16) -> uint16 {
    if b <= a { ((a as uint16) - (b as uint16)) as uint16 } else { ((b as uint16) - (a as uint16)) as uint16 }
}
```

### `i16::unsigned_abs`

```click
function unsigned_abs(a: int16) -> uint16 {
    if a < (0i64 as int16) { ((0u32 as uint16) - (a as uint16)) as uint16 } else { a as uint16 }
}
```

### `i32::min`

```click
function min(a: int32, b: int32) -> int32 {
    if a <= b { a } else { b }
}
```

### `i32::max`

```click
function max(a: int32, b: int32) -> int32 {
    if a <= b { b } else { a }
}
```

### `i32::wrapping_add`

```click
function wrapping_add(a: int32, b: int32) -> int32 {
    ((a as uint32) + (b as uint32)) as int32
}
```

### `i32::wrapping_sub`

```click
function wrapping_sub(a: int32, b: int32) -> int32 {
    ((a as uint32) - (b as uint32)) as int32
}
```

### `i32::wrapping_mul`

```click
function wrapping_mul(a: int32, b: int32) -> int32 {
    ((a as uint32) * (b as uint32)) as int32
}
```

### `i32::saturating_add`

```click
function saturating_add(a: int32, b: int32) -> int32 {
    if to_integer(a) + to_integer(b) > 2147483647 {
        (2147483647i64 as int32)
    } else {
        if to_integer(a) + to_integer(b) < -2147483648 {
            (-2147483648i64 as int32)
        } else {
            ((a as uint32) + (b as uint32)) as int32
        }
    }
}
```

### `i32::saturating_sub`

```click
function saturating_sub(a: int32, b: int32) -> int32 {
    if to_integer(a) - to_integer(b) > 2147483647 {
        (2147483647i64 as int32)
    } else {
        if to_integer(a) - to_integer(b) < -2147483648 {
            (-2147483648i64 as int32)
        } else {
            ((a as uint32) - (b as uint32)) as int32
        }
    }
}
```

### `i32::checked_add`

```click
function checked_add(a: int32, b: int32) -> Option<int32> {
    if -2147483648 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 2147483647 {
        Option<int32>::Some(((a as uint32) + (b as uint32)) as int32)
    } else {
        Option<int32>::None
    }
}
```

### `i32::checked_sub`

```click
function checked_sub(a: int32, b: int32) -> Option<int32> {
    if -2147483648 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 2147483647 {
        Option<int32>::Some(((a as uint32) - (b as uint32)) as int32)
    } else {
        Option<int32>::None
    }
}
```

### `i32::abs_diff`

```click
function abs_diff(a: int32, b: int32) -> uint32 {
    if b <= a { (a as uint32) - (b as uint32) } else { (b as uint32) - (a as uint32) }
}
```

### `i32::unsigned_abs`

```click
function unsigned_abs(a: int32) -> uint32 {
    if a < (0i64 as int32) { 0u32 - (a as uint32) } else { a as uint32 }
}
```

### `i64::min`

```click
function min(a: int64, b: int64) -> int64 {
    if a <= b { a } else { b }
}
```

### `i64::max`

```click
function max(a: int64, b: int64) -> int64 {
    if a <= b { b } else { a }
}
```

### `i64::wrapping_add`

```click
function wrapping_add(a: int64, b: int64) -> int64 {
    ((a as uint64) + (b as uint64)) as int64
}
```

### `i64::wrapping_sub`

```click
function wrapping_sub(a: int64, b: int64) -> int64 {
    ((a as uint64) - (b as uint64)) as int64
}
```

### `i64::wrapping_mul`

```click
function wrapping_mul(a: int64, b: int64) -> int64 {
    ((a as uint64) * (b as uint64)) as int64
}
```

### `i64::saturating_add`

```click
function saturating_add(a: int64, b: int64) -> int64 {
    if to_integer(a) + to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) + to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) + (b as uint64)) as int64
        }
    }
}
```

### `i64::saturating_sub`

```click
function saturating_sub(a: int64, b: int64) -> int64 {
    if to_integer(a) - to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) - to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) - (b as uint64)) as int64
        }
    }
}
```

### `i64::checked_add`

```click
function checked_add(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) + (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `i64::checked_sub`

```click
function checked_sub(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) - (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `i64::abs_diff`

```click
function abs_diff(a: int64, b: int64) -> uint64 {
    if b <= a { (a as uint64) - (b as uint64) } else { (b as uint64) - (a as uint64) }
}
```

### `i64::unsigned_abs`

```click
function unsigned_abs(a: int64) -> uint64 {
    if a < 0i64 { 0u64 - (a as uint64) } else { a as uint64 }
}
```

### `isize::min`

```click
function min(a: int64, b: int64) -> int64 {
    if a <= b { a } else { b }
}
```

### `isize::max`

```click
function max(a: int64, b: int64) -> int64 {
    if a <= b { b } else { a }
}
```

### `isize::wrapping_add`

```click
function wrapping_add(a: int64, b: int64) -> int64 {
    ((a as uint64) + (b as uint64)) as int64
}
```

### `isize::wrapping_sub`

```click
function wrapping_sub(a: int64, b: int64) -> int64 {
    ((a as uint64) - (b as uint64)) as int64
}
```

### `isize::wrapping_mul`

```click
function wrapping_mul(a: int64, b: int64) -> int64 {
    ((a as uint64) * (b as uint64)) as int64
}
```

### `isize::saturating_add`

```click
function saturating_add(a: int64, b: int64) -> int64 {
    if to_integer(a) + to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) + to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) + (b as uint64)) as int64
        }
    }
}
```

### `isize::saturating_sub`

```click
function saturating_sub(a: int64, b: int64) -> int64 {
    if to_integer(a) - to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) - to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) - (b as uint64)) as int64
        }
    }
}
```

### `isize::checked_add`

```click
function checked_add(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) + (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `isize::checked_sub`

```click
function checked_sub(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) - (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `isize::abs_diff`

```click
function abs_diff(a: int64, b: int64) -> uint64 {
    if b <= a { (a as uint64) - (b as uint64) } else { (b as uint64) - (a as uint64) }
}
```

### `isize::unsigned_abs`

```click
function unsigned_abs(a: int64) -> uint64 {
    if a < 0i64 { 0u64 - (a as uint64) } else { a as uint64 }
}
```

### `u8::min`

```click
function min(a: uint8, b: uint8) -> uint8 {
    if a <= b { a } else { b }
}
```

### `u8::max`

```click
function max(a: uint8, b: uint8) -> uint8 {
    if a <= b { b } else { a }
}
```

### `u8::wrapping_add`

```click
function wrapping_add(a: uint8, b: uint8) -> uint8 {
    a + b
}
```

### `u8::wrapping_sub`

```click
function wrapping_sub(a: uint8, b: uint8) -> uint8 {
    a - b
}
```

### `u8::wrapping_mul`

```click
function wrapping_mul(a: uint8, b: uint8) -> uint8 {
    a * b
}
```

### `u8::saturating_add`

```click
function saturating_add(a: uint8, b: uint8) -> uint8 {
    if to_integer(a) + to_integer(b) <= 255 { (a + b) as uint8 } else { (255u32 as uint8) }
}
```

### `u8::saturating_sub`

```click
function saturating_sub(a: uint8, b: uint8) -> uint8 {
    if b <= a { (a - b) as uint8 } else { (0u32 as uint8) }
}
```

### `u8::checked_add`

```click
function checked_add(a: uint8, b: uint8) -> Option<uint8> {
    if to_integer(a) + to_integer(b) <= 255 {
        Option<uint8>::Some((a + b) as uint8)
    } else {
        Option<uint8>::None
    }
}
```

### `u8::checked_sub`

```click
function checked_sub(a: uint8, b: uint8) -> Option<uint8> {
    if b <= a { Option<uint8>::Some((a - b) as uint8) } else { Option<uint8>::None }
}
```

### `u8::abs_diff`

```click
function abs_diff(a: uint8, b: uint8) -> uint8 {
    if b <= a { (a - b) as uint8 } else { (b - a) as uint8 }
}
```

### `u16::min`

```click
function min(a: uint16, b: uint16) -> uint16 {
    if a <= b { a } else { b }
}
```

### `u16::max`

```click
function max(a: uint16, b: uint16) -> uint16 {
    if a <= b { b } else { a }
}
```

### `u16::wrapping_add`

```click
function wrapping_add(a: uint16, b: uint16) -> uint16 {
    a + b
}
```

### `u16::wrapping_sub`

```click
function wrapping_sub(a: uint16, b: uint16) -> uint16 {
    a - b
}
```

### `u16::wrapping_mul`

```click
function wrapping_mul(a: uint16, b: uint16) -> uint16 {
    a * b
}
```

### `u16::saturating_add`

```click
function saturating_add(a: uint16, b: uint16) -> uint16 {
    if to_integer(a) + to_integer(b) <= 65535 { (a + b) as uint16 } else { (65535u32 as uint16) }
}
```

### `u16::saturating_sub`

```click
function saturating_sub(a: uint16, b: uint16) -> uint16 {
    if b <= a { (a - b) as uint16 } else { (0u32 as uint16) }
}
```

### `u16::checked_add`

```click
function checked_add(a: uint16, b: uint16) -> Option<uint16> {
    if to_integer(a) + to_integer(b) <= 65535 {
        Option<uint16>::Some((a + b) as uint16)
    } else {
        Option<uint16>::None
    }
}
```

### `u16::checked_sub`

```click
function checked_sub(a: uint16, b: uint16) -> Option<uint16> {
    if b <= a { Option<uint16>::Some((a - b) as uint16) } else { Option<uint16>::None }
}
```

### `u16::abs_diff`

```click
function abs_diff(a: uint16, b: uint16) -> uint16 {
    if b <= a { (a - b) as uint16 } else { (b - a) as uint16 }
}
```

### `u32::min`

```click
function min(a: uint32, b: uint32) -> uint32 {
    if a <= b { a } else { b }
}
```

### `u32::max`

```click
function max(a: uint32, b: uint32) -> uint32 {
    if a <= b { b } else { a }
}
```

### `u32::wrapping_add`

```click
function wrapping_add(a: uint32, b: uint32) -> uint32 {
    a + b
}
```

### `u32::wrapping_sub`

```click
function wrapping_sub(a: uint32, b: uint32) -> uint32 {
    a - b
}
```

### `u32::wrapping_mul`

```click
function wrapping_mul(a: uint32, b: uint32) -> uint32 {
    a * b
}
```

### `u32::saturating_add`

```click
function saturating_add(a: uint32, b: uint32) -> uint32 {
    if to_integer(a) + to_integer(b) <= 4294967295 { a + b } else { 4294967295u32 }
}
```

### `u32::saturating_sub`

```click
function saturating_sub(a: uint32, b: uint32) -> uint32 {
    if b <= a { a - b } else { 0u32 }
}
```

### `u32::checked_add`

```click
function checked_add(a: uint32, b: uint32) -> Option<uint32> {
    if to_integer(a) + to_integer(b) <= 4294967295 {
        Option<uint32>::Some(a + b)
    } else {
        Option<uint32>::None
    }
}
```

### `u32::checked_sub`

```click
function checked_sub(a: uint32, b: uint32) -> Option<uint32> {
    if b <= a { Option<uint32>::Some(a - b) } else { Option<uint32>::None }
}
```

### `u32::abs_diff`

```click
function abs_diff(a: uint32, b: uint32) -> uint32 {
    if b <= a { a - b } else { b - a }
}
```

### `u32::multiply_to_integer`

```click
theorem multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(integer::uint32_multiply_to_integer(left, right));
}
```

An in-range `u32` product is the Integer product: the Rust name of
[`integer::uint32_multiply_to_integer`](#integeruint32_multiply_to_integer),
proved by applying it.

**Verified use:** [`examples/rust-unsigned/arithmetic.click`](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.click), [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `u64::min`

```click
function min(a: uint64, b: uint64) -> uint64 {
    if a <= b { a } else { b }
}
```

### `u64::max`

```click
function max(a: uint64, b: uint64) -> uint64 {
    if a <= b { b } else { a }
}
```

### `u64::wrapping_add`

```click
function wrapping_add(a: uint64, b: uint64) -> uint64 {
    a + b
}
```

### `u64::wrapping_sub`

```click
function wrapping_sub(a: uint64, b: uint64) -> uint64 {
    a - b
}
```

### `u64::wrapping_mul`

```click
function wrapping_mul(a: uint64, b: uint64) -> uint64 {
    a * b
}
```

### `u64::saturating_add`

```click
function saturating_add(a: uint64, b: uint64) -> uint64 {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 { a + b } else { 18446744073709551615u64 }
}
```

### `u64::saturating_sub`

```click
function saturating_sub(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { 0u64 }
}
```

### `u64::checked_add`

```click
function checked_add(a: uint64, b: uint64) -> Option<uint64> {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 {
        Option<uint64>::Some(a + b)
    } else {
        Option<uint64>::None
    }
}
```

### `u64::checked_sub`

```click
function checked_sub(a: uint64, b: uint64) -> Option<uint64> {
    if b <= a { Option<uint64>::Some(a - b) } else { Option<uint64>::None }
}
```

### `u64::abs_diff`

```click
function abs_diff(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { b - a }
}
```

### `usize::min`

```click
function min(a: uint64, b: uint64) -> uint64 {
    if a <= b { a } else { b }
}
```

### `usize::max`

```click
function max(a: uint64, b: uint64) -> uint64 {
    if a <= b { b } else { a }
}
```

### `usize::wrapping_add`

```click
function wrapping_add(a: uint64, b: uint64) -> uint64 {
    a + b
}
```

### `usize::wrapping_sub`

```click
function wrapping_sub(a: uint64, b: uint64) -> uint64 {
    a - b
}
```

### `usize::wrapping_mul`

```click
function wrapping_mul(a: uint64, b: uint64) -> uint64 {
    a * b
}
```

### `usize::saturating_add`

```click
function saturating_add(a: uint64, b: uint64) -> uint64 {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 { a + b } else { 18446744073709551615u64 }
}
```

### `usize::saturating_sub`

```click
function saturating_sub(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { 0u64 }
}
```

### `usize::checked_add`

```click
function checked_add(a: uint64, b: uint64) -> Option<uint64> {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 {
        Option<uint64>::Some(a + b)
    } else {
        Option<uint64>::None
    }
}
```

### `usize::checked_sub`

```click
function checked_sub(a: uint64, b: uint64) -> Option<uint64> {
    if b <= a { Option<uint64>::Some(a - b) } else { Option<uint64>::None }
}
```

### `usize::abs_diff`

```click
function abs_diff(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { b - a }
}
```

### `usize::product_bound_from_division`

```click
theorem product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by apply(integer::uint64_product_bound_from_division(x, y));
}
```

A product bounded by division does not exceed `usize::MAX`: the Rust name of
[`integer::uint64_product_bound_from_division`](#integeruint64_product_bound_from_division),
proved by applying it.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md); `tests/rust_import.rs` applies it to imported Rust (`rust_usize_arithmetic_casts_and_expansion_verify`).

### `usize::multiply_to_integer`

```click
theorem multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(integer::uint64_multiply_to_integer(left, right));
}
```

An in-range `usize` product is the Integer product: the Rust name of
[`integer::uint64_multiply_to_integer`](#integeruint64_multiply_to_integer),
proved by applying it.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md); `tests/rust_import.rs` applies it to imported Rust (`rust_usize_arithmetic_casts_and_expansion_verify`).

## `click::rust::option`

The proof helper in `library/rust/option.click` states the result of Rust's
`Option::unwrap_or`.

### `option::unwrap_or`

```click
function unwrap_or<T>(o: Option<T>, default: T) -> T {
    match o {
        Option::Some(value) => value,
        Option::None => default,
    }
}
```

`unwrap_or` returns the payload of `Some` or the supplied default.
A sidecar can write `click::rust::option::unwrap_or(o, d)` or selectively
import it with `import click::rust::option::{unwrap_or};`.

**Verified use:** [`core-methods/methods.click`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.click).

## `click::rust::result`

The proof helper in `library/rust/result.click` states the result of Rust's
`Result::unwrap_or`.

### `result::unwrap_or`

```click
function unwrap_or<T, E>(r: Result<T, E>, default: T) -> T {
    match r {
        Result::Ok(value) => value,
        Result::Err(error) => default,
    }
}
```

`unwrap_or` returns the payload of `Ok` or the supplied default.
A sidecar can write `click::rust::result::unwrap_or(r, d)` or selectively
import it with `import click::rust::result::{unwrap_or};`.

**Verified use:** [`result-values/results.click`](https://github.com/clicklang/click/blob/master/design/charon-trial/result-values/results.click).

## `click::rust::vec`

Source: `library/rust/vec.click`, `import click::rust::vec;`.

### Rust vectors

`click::rust::vec` declares `Vec<T>`, the values a Rust vector holds, as a
primitive library type, with four operations and the axioms that relate them.
A sidecar reads them after `import click::rust::vec;` and proves claims about
vectors by citing the axioms, `apply(vec::len_push(v, x));`. The `type`, the
bodyless `function`s and the `axiom`s are forms only the built-in library
modules may declare; each axiom is trusted, not proved
([trust](../../concepts/trust.md#the-click-library)). Capacity and allocation
are outside the model.
A Rust `Vec<u32>` an import reads is this type at `uint32`, and its methods'
contracts are stated with these operations
([Vec values](../rust.md#vec-values)).

### `Vec`

```click
type Vec<T>;
```

A Rust vector's values: a finite sequence of fewer than 2^64 values of `T`. It is a primitive type, like `uint32`: it has no constructors, so a `match`, a proof `match` and `induct` refuse it, and the kernel reads each instance, `Vec<uint32>`, as a rigid type of its own. Its meaning is the four operations below and the axioms that relate them; two vectors that hold the same values are equal by `vec::extensionality`. A `spec enum` field cannot hold a `Vec` yet.

### `vec::len`

```click
function len<T>(v: Vec<T>) -> uint64;
```

The number of values in `v`. Opaque: `unfold` refuses it, since it has no definition.

### `vec::get`

```click
function get<T>(v: Vec<T>, i: uint64) -> T;
```

The value at index `i`. The axioms describe it only below `vec::len(v)`; past the end it names a value nothing constrains.

### `vec::push`

```click
function push<T>(v: Vec<T>, x: T) -> Vec<T>;
```

`v` with `x` appended.

### `vec::set`

```click
function set<T>(v: Vec<T>, i: uint64, x: T) -> Vec<T>;
```

`v` with the value at index `i` replaced by `x`. The axioms describe it only for `i` below `vec::len(v)`.

### `vec::len_push`

```click
axiom len_push<T>(v: Vec<T>, x: T) {
    requires vec::len(v) < 18446744073709551615u64;
    ensures vec::len(vec::push(v, x)) == vec::len(v) + 1;
}
```

**Axiom:** trusted, not proved.

### `vec::get_push_last`

```click
axiom get_push_last<T>(v: Vec<T>, x: T) {
    requires vec::len(v) < 18446744073709551615u64;
    ensures vec::get(vec::push(v, x), vec::len(v)) == x;
}
```

**Axiom:** trusted, not proved.

### `vec::get_push_kept`

```click
axiom get_push_kept<T>(v: Vec<T>, x: T, i: uint64) {
    requires i < vec::len(v);
    ensures vec::get(vec::push(v, x), i) == vec::get(v, i);
}
```

**Axiom:** trusted, not proved.

### `vec::len_set`

```click
axiom len_set<T>(v: Vec<T>, i: uint64, x: T) {
    requires i < vec::len(v);
    ensures vec::len(vec::set(v, i, x)) == vec::len(v);
}
```

**Axiom:** trusted, not proved.

### `vec::get_set_same`

```click
axiom get_set_same<T>(v: Vec<T>, i: uint64, x: T) {
    requires i < vec::len(v);
    ensures vec::get(vec::set(v, i, x), i) == x;
}
```

**Axiom:** trusted, not proved.

### `vec::get_set_other`

```click
axiom get_set_other<T>(v: Vec<T>, i: uint64, j: uint64, x: T) {
    requires i < vec::len(v);
    requires j < vec::len(v);
    requires i != j;
    ensures vec::get(vec::set(v, i, x), j) == vec::get(v, j);
}
```

**Axiom:** trusted, not proved.

### `vec::extensionality`

```click
axiom extensionality<T>(v: Vec<T>, w: Vec<T>) {
    requires vec::len(v) == vec::len(w);
    requires forall (i: uint64) { i < vec::len(v) implies vec::get(v, i) == vec::get(w, i) };
    ensures v == w;
}
```

**Axiom:** trusted, not proved.

## `click::rust::slice`

Source: `library/rust/slice.click`, `import click::rust::slice;`.

### Rust slices

`click::rust::slice` declares `Slice<T>`, a Rust slice as one value: its data
pointer and its length. `==` on slices is identity, the same pointer and the
same length. A slice value grants no access: reading `s[i]` reads memory
through its pointer under the caller's `views` or `owns`. A sidecar names
these operations after `import click::rust::slice;`. A Rust sidecar writes a
slice with Rust's syntax, and each slice is one argument of a pure-function
call, so a pointer and a length are passed as `slice::from_raw_parts(p, n)`
([pure functions](../rust.md)). A slice parameter is lowered as its pointer
and its length; both forms are the same slice.

### `Slice`

```click
spec enum Slice<T> {
    Slice(T*, uint64),
}
```

A slice of `T`: a pointer to its first element and its number of elements.
Two slices are equal exactly when their pointers and lengths are.

### `slice::len`

```click
function len<T>(s: Slice<T>) -> uint64 {
    match s {
        Slice::Slice(_, n) => n,
    }
}
```

The number of elements, Rust's `s.len()`.

### `slice::as_ptr`

```click
function as_ptr<T>(s: Slice<T>) -> T* {
    match s {
        Slice::Slice(p, _) => p,
    }
}
```

The data pointer, Rust's `s.as_ptr()`.

### `slice::from_raw_parts`

```click
function from_raw_parts<T>(p: T*, n: uint64) -> Slice<T> {
    Slice::Slice(p, n)
}
```

The slice with data `p` and length `n`, Rust's
`core::slice::from_raw_parts(p, n)`.

### `slice::subslice_len`

```click
function subslice_len(start: uint64, end: uint64, len: uint64) -> uint64 {
    end - start
}
```

The length of the subslice `s[start..end]` of a slice of length `len`. A
call owes `start <= end` and `end <= len` where it is evaluated, guarded as
every evaluation condition is, where Rust panics otherwise. A Rust sidecar's
subslice `s[a..b]` is `Slice::Slice(s.as_ptr() + a, slice::subslice_len(a,
b, s.len()))`, and prints as `s[a..b]`.


## Rust core interfaces

Source: `library/rust/core.interface.click`. This file is not a module: the Rust
importer appends it to a sidecar when an import calls one of its methods,
and writes each generic `extern fn` block out at each element type a call
names, `Vec::push<u32>`. A block no call names is dropped. The integer
core-method contracts are in [Rust integer methods](#rust-integer-methods).

### `Vec<T>` methods

```click
fn Vec::new<T>() -> Vec<T> {
    ensures click::rust::vec::len(result) == 0u64;
}
fn Vec::with_capacity<T>(capacity: usize) -> Vec<T> {
    ensures click::rust::vec::len(result) == 0u64;
}
fn Vec::push<T>(v: &mut Vec<T>, x: T) {
    owns *v;
    requires click::rust::vec::len(*v) < 18446744073709551615u64;
    ensures *v == click::rust::vec::push(old(*v), x);
    ensures click::rust::vec::len(*v) == click::rust::vec::len(old(*v)) + 1;
    ensures click::rust::vec::get(*v, click::rust::vec::len(old(*v))) == x;
    ensures forall (k: usize) { k < click::rust::vec::len(old(*v)) implies click::rust::vec::get(*v, k) == click::rust::vec::get(old(*v), k) };
}
fn Vec::len<T>(v: &Vec<T>) -> usize {
    views *v;
    ensures result == click::rust::vec::len(old(*v));
}
fn Vec::index<T>(v: &Vec<T>, i: usize) -> T {
    views *v;
    requires i < click::rust::vec::len(*v);
    ensures result == click::rust::vec::get(old(*v), i);
}
```

**Meaning:** Each call's effect on the library's `Vec<T>` value
([`click::rust::vec`](#clickrustvec)). The capacity is outside the model.
`v[i]` requires `i` in bounds, as Rust panics otherwise. A vector holds at
most `u64::MAX` elements, and `push` requires room below it; Rust's own
allocation limit is smaller and aborts rather than returns.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies [`design/charon-trial/vec-values/vecs.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/vec-values/vecs.rs) in `charon_vec_values_read_as_the_library_vec`, and refuses each claim mutated false and an index not shown in bounds.

### `Box<T>`

```click
type Box<T> {
    owns allocation(self, sizeof(T));
    owns *self;
}
fn Box::new<T>(x: T) -> Box<T> {
    allocates(result, sizeof(T));
    produces *result;
    ensures result != 0;
    ensures aligned(result, alignof(T));
    ensures *result == x;
}
fn Box::drop<T>(b: Box<T>) {
    consumes allocation(b, sizeof(T));
    consumes uninitialized(*b);
}
```

**Meaning:** A box owns its allocation, `sizeof(T)` bytes, and the value in
it: its [type resource](../rust.md#type-resources), `Box<R>(b)`, holds
both. `Box::new(x)` moves `x` into an allocation the call creates
([fresh allocations](../language/c.md#fresh-allocations)); allocation
failure aborts, so it returns only a non-null box. `Box::drop(b)` is
`<Box<T> as Drop>::drop`, which the compiler calls after the contents'
drop glue or after they were moved out, and frees the allocation; it needs
the box's storage, initialized or not, and no alignment. The importer calls
these for `Box::new` and for each box's drop, at the boxed struct
(`Box::new<boxed::Cell>`), symbolic layouts included
([Boxes](../rust.md#boxes)).

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies [`design/charon-trial/boxes`](https://github.com/clicklang/click/blob/master/design/charon-trial/boxes/boxed.rs) in `charon_boxes_allocate_read_write_and_free_their_struct`, [`design/charon-trial/recursive-drop`](https://github.com/clicklang/click/blob/master/design/charon-trial/recursive-drop/list.rs) in `charon_recursive_drop_frees_every_node`, and [`design/charon-trial/generic-stack`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-stack/stack.rs) in `charon_generic_stack_verifies_once_for_every_type`.

### `slice::swap<T>`

```click
fn slice::swap<T>(s: &mut [T], a: usize, b: usize) {
    owns *s;
    requires a < s.len();
    requires b < s.len();
    ensures s[a] == old(s[b]);
    ensures s[b] == old(s[a]);
    ensures forall (k: usize) { k < s.len() and k != a and k != b implies s[k] == old(s[k]) };
}
```

**Meaning:** `<[T]>::swap(s, a, b)` owns the slice, requires both indices in
bounds, as Rust panics otherwise, and exchanges the two elements, leaving
every other element unchanged.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `exchange`, `swap_bytes` and `reverse_three` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs), and refuses a `swap` index not shown in bounds.

### `Option::take<T>`

```click
fn Option::take<T>(o: &mut Option<T>) -> Option<T> {
    owns *o;
    ensures result == old(*o);
    ensures *o == Option<T>::None;
}
```

**Meaning:** `o.take()` is `mem::replace(o, None)`: it returns the option
`*o` held and leaves `None` there. The importer declares it at a scalar
payload, `Option::take<u32>`; an option of a box is still lowered to the move
the call makes ([Boxes](../rust.md#boxes)).

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies `scalar_taken` and `take_param` in [`design/charon-trial/option-take/take.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/option-take/take.rs) in `charon_option_take_moves_out_and_leaves_none`.

### `Option<T>` and `Result<T, E>` unwrapping

```click
fn Option::unwrap<T>(o: Option<T>) -> T {
    requires o != Option<T>::None;
    ensures o == Option<T>::Some(result);
}
fn Option::expect<T>(o: Option<T>) -> T {
    requires o != Option<T>::None;
    ensures o == Option<T>::Some(result);
}
fn Option::unwrap_or<T>(o: Option<T>, d: T) -> T {
    ensures result == click::rust::option::unwrap_or(o, d);
}
fn Result::unwrap<T, E>(r: Result<T, E>) -> T {
    requires exists (value: T) { r == Result<T, E>::Ok(value) };
    ensures r == Result<T, E>::Ok(result);
}
fn Result::expect<T, E>(r: Result<T, E>) -> T {
    requires exists (value: T) { r == Result<T, E>::Ok(value) };
    ensures r == Result<T, E>::Ok(result);
}
fn Result::unwrap_or<T, E>(r: Result<T, E>, d: T) -> T {
    ensures result == click::rust::result::unwrap_or(r, d);
}
```

**Meaning:** `unwrap` and `expect` require `Some` or `Ok`, as Rust panics
otherwise, and return its payload; `expect`'s message serves the panic alone
and is not passed. `unwrap_or` is the library's `option::unwrap_or` or
`result::unwrap_or`. The importer declares them at a scalar payload.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/panics.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/panics.rs) verifies `unwrapped` and `expected` in [`design/charon-trial/panics/panics.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/panics/panics.rs) and refuses an unwrap not shown `Some`; [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies `Result` `unwrap`, `expect` and `unwrap_or` in [`design/charon-trial/result-values/results.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/result-values/results.rs) in `charon_result_values_read_as_click_results`; [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `Option::unwrap_or` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs).

## Rust integer methods

Source: `library/rust/integers.interface.click`, one contract per Rust integer core
method and type, each on one line. This file is not a module: the Rust
importer appends to a sidecar the line of each method an import calls, and
only those, so a contract at a type no call names, `Option<i8>`, is never
read. Each states its result with the specification function of the same
path in [`click::rust::i8` through `click::rust::usize`](#clickrusti8-through-clickrustusize);
the `extern`'s own path, `u32::min`, names the program's function, never the
library function ([core library methods](../rust.md#core-library-methods)).

### Integer `min` and `max`

```click
fn i8::min(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::min(a, b); }
fn i8::max(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::max(a, b); }
fn i16::min(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::min(a, b); }
fn i16::max(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::max(a, b); }
fn i32::min(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::min(a, b); }
fn i32::max(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::max(a, b); }
fn i64::min(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::min(a, b); }
fn i64::max(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::max(a, b); }
fn isize::min(a: isize, b: isize) -> isize { ensures result == click::rust::isize::min(a, b); }
fn isize::max(a: isize, b: isize) -> isize { ensures result == click::rust::isize::max(a, b); }
fn u8::min(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::min(a, b); }
fn u8::max(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::max(a, b); }
fn u16::min(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::min(a, b); }
fn u16::max(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::max(a, b); }
fn u32::min(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::min(a, b); }
fn u32::max(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::max(a, b); }
fn u64::min(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::min(a, b); }
fn u64::max(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::max(a, b); }
fn usize::min(a: usize, b: usize) -> usize { ensures result == click::rust::usize::min(a, b); }
fn usize::max(a: usize, b: usize) -> usize { ensures result == click::rust::usize::max(a, b); }
```

**Meaning:** `a.min(b)` and `a.max(b)`, of `Ord` at an integer type, are the library's
`min` and `max` of that type.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `smaller`, `larger` and `fewer` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs), and refuses a wrong claim about `smaller(1, 2)`.

### Integer wrapping arithmetic

```click
fn i8::wrapping_add(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_add(a, b); }
fn i8::wrapping_sub(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_sub(a, b); }
fn i8::wrapping_mul(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_mul(a, b); }
fn i16::wrapping_add(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_add(a, b); }
fn i16::wrapping_sub(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_sub(a, b); }
fn i16::wrapping_mul(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_mul(a, b); }
fn i32::wrapping_add(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_add(a, b); }
fn i32::wrapping_sub(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_sub(a, b); }
fn i32::wrapping_mul(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_mul(a, b); }
fn i64::wrapping_add(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_add(a, b); }
fn i64::wrapping_sub(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_sub(a, b); }
fn i64::wrapping_mul(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_mul(a, b); }
fn isize::wrapping_add(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_add(a, b); }
fn isize::wrapping_sub(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_sub(a, b); }
fn isize::wrapping_mul(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_mul(a, b); }
fn u8::wrapping_add(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_add(a, b); }
fn u8::wrapping_sub(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_sub(a, b); }
fn u8::wrapping_mul(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_mul(a, b); }
fn u16::wrapping_add(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_add(a, b); }
fn u16::wrapping_sub(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_sub(a, b); }
fn u16::wrapping_mul(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_mul(a, b); }
fn u32::wrapping_add(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_add(a, b); }
fn u32::wrapping_sub(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_sub(a, b); }
fn u32::wrapping_mul(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_mul(a, b); }
fn u64::wrapping_add(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_add(a, b); }
fn u64::wrapping_sub(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_sub(a, b); }
fn u64::wrapping_mul(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_mul(a, b); }
fn usize::wrapping_add(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_add(a, b); }
fn usize::wrapping_sub(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_sub(a, b); }
fn usize::wrapping_mul(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_mul(a, b); }
```

**Meaning:** `wrapping_add`, `wrapping_sub` and `wrapping_mul` are the library's
modular sums, differences and products of each type.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `byte_ring` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs); [`tests/examples.rs`](https://github.com/clicklang/click/blob/master/tests/examples.rs) verifies `wrapping_add_u32`, `wrapping_sub_u32` and `wrapping_mul_u32` in [`examples/integer-languages/rust/integers.rs`](https://github.com/clicklang/click/blob/master/examples/integer-languages/rust/integers.rs) in `example_projects`.

### Integer saturating arithmetic

```click
fn i8::saturating_add(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::saturating_add(a, b); }
fn i8::saturating_sub(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::saturating_sub(a, b); }
fn i16::saturating_add(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::saturating_add(a, b); }
fn i16::saturating_sub(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::saturating_sub(a, b); }
fn i32::saturating_add(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::saturating_add(a, b); }
fn i32::saturating_sub(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::saturating_sub(a, b); }
fn i64::saturating_add(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::saturating_add(a, b); }
fn i64::saturating_sub(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::saturating_sub(a, b); }
fn isize::saturating_add(a: isize, b: isize) -> isize { ensures result == click::rust::isize::saturating_add(a, b); }
fn isize::saturating_sub(a: isize, b: isize) -> isize { ensures result == click::rust::isize::saturating_sub(a, b); }
fn u8::saturating_add(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::saturating_add(a, b); }
fn u8::saturating_sub(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::saturating_sub(a, b); }
fn u16::saturating_add(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::saturating_add(a, b); }
fn u16::saturating_sub(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::saturating_sub(a, b); }
fn u32::saturating_add(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::saturating_add(a, b); }
fn u32::saturating_sub(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::saturating_sub(a, b); }
fn u64::saturating_add(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::saturating_add(a, b); }
fn u64::saturating_sub(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::saturating_sub(a, b); }
fn usize::saturating_add(a: usize, b: usize) -> usize { ensures result == click::rust::usize::saturating_add(a, b); }
fn usize::saturating_sub(a: usize, b: usize) -> usize { ensures result == click::rust::usize::saturating_sub(a, b); }
```

**Meaning:** `saturating_add` and `saturating_sub` are the library's sums and
differences clamped to the type's range.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `shortfall` and `sample_sum` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs).

### Integer checked arithmetic

```click
fn i8::checked_add(a: i8, b: i8) -> Option<i8> { ensures result == click::rust::i8::checked_add(a, b); }
fn i8::checked_sub(a: i8, b: i8) -> Option<i8> { ensures result == click::rust::i8::checked_sub(a, b); }
fn i16::checked_add(a: i16, b: i16) -> Option<i16> { ensures result == click::rust::i16::checked_add(a, b); }
fn i16::checked_sub(a: i16, b: i16) -> Option<i16> { ensures result == click::rust::i16::checked_sub(a, b); }
fn i32::checked_add(a: i32, b: i32) -> Option<i32> { ensures result == click::rust::i32::checked_add(a, b); }
fn i32::checked_sub(a: i32, b: i32) -> Option<i32> { ensures result == click::rust::i32::checked_sub(a, b); }
fn i64::checked_add(a: i64, b: i64) -> Option<i64> { ensures result == click::rust::i64::checked_add(a, b); }
fn i64::checked_sub(a: i64, b: i64) -> Option<i64> { ensures result == click::rust::i64::checked_sub(a, b); }
fn isize::checked_add(a: isize, b: isize) -> Option<isize> { ensures result == click::rust::isize::checked_add(a, b); }
fn isize::checked_sub(a: isize, b: isize) -> Option<isize> { ensures result == click::rust::isize::checked_sub(a, b); }
fn u8::checked_add(a: u8, b: u8) -> Option<u8> { ensures result == click::rust::u8::checked_add(a, b); }
fn u8::checked_sub(a: u8, b: u8) -> Option<u8> { ensures result == click::rust::u8::checked_sub(a, b); }
fn u16::checked_add(a: u16, b: u16) -> Option<u16> { ensures result == click::rust::u16::checked_add(a, b); }
fn u16::checked_sub(a: u16, b: u16) -> Option<u16> { ensures result == click::rust::u16::checked_sub(a, b); }
fn u32::checked_add(a: u32, b: u32) -> Option<u32> { ensures result == click::rust::u32::checked_add(a, b); }
fn u32::checked_sub(a: u32, b: u32) -> Option<u32> { ensures result == click::rust::u32::checked_sub(a, b); }
fn u64::checked_add(a: u64, b: u64) -> Option<u64> { ensures result == click::rust::u64::checked_add(a, b); }
fn u64::checked_sub(a: u64, b: u64) -> Option<u64> { ensures result == click::rust::u64::checked_sub(a, b); }
fn usize::checked_add(a: usize, b: usize) -> Option<usize> { ensures result == click::rust::usize::checked_add(a, b); }
fn usize::checked_sub(a: usize, b: usize) -> Option<usize> { ensures result == click::rust::usize::checked_sub(a, b); }
```

**Meaning:** `checked_add` and `checked_sub` return the library's `Option` of the
type: `Some` of the sum or difference when it is in range, `None`
otherwise.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `clamp_add` and `spend` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs), and refuses a fitting sum claimed `None`.

### Integer `abs_diff` and `unsigned_abs`

```click
fn i8::abs_diff(a: i8, b: i8) -> u8 { ensures result == click::rust::i8::abs_diff(a, b); }
fn i8::unsigned_abs(a: i8) -> u8 { ensures result == click::rust::i8::unsigned_abs(a); }
fn i16::abs_diff(a: i16, b: i16) -> u16 { ensures result == click::rust::i16::abs_diff(a, b); }
fn i16::unsigned_abs(a: i16) -> u16 { ensures result == click::rust::i16::unsigned_abs(a); }
fn i32::abs_diff(a: i32, b: i32) -> u32 { ensures result == click::rust::i32::abs_diff(a, b); }
fn i32::unsigned_abs(a: i32) -> u32 { ensures result == click::rust::i32::unsigned_abs(a); }
fn i64::abs_diff(a: i64, b: i64) -> u64 { ensures result == click::rust::i64::abs_diff(a, b); }
fn i64::unsigned_abs(a: i64) -> u64 { ensures result == click::rust::i64::unsigned_abs(a); }
fn isize::abs_diff(a: isize, b: isize) -> usize { ensures result == click::rust::isize::abs_diff(a, b); }
fn isize::unsigned_abs(a: isize) -> usize { ensures result == click::rust::isize::unsigned_abs(a); }
fn u8::abs_diff(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::abs_diff(a, b); }
fn u16::abs_diff(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::abs_diff(a, b); }
fn u32::abs_diff(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::abs_diff(a, b); }
fn u64::abs_diff(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::abs_diff(a, b); }
fn usize::abs_diff(a: usize, b: usize) -> usize { ensures result == click::rust::usize::abs_diff(a, b); }
```

**Meaning:** `abs_diff` is the distance between its operands and `unsigned_abs` the
magnitude of a signed value, each in the unsigned type of the operand's
width.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `distance` and `magnitude` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs).

## `click::separation`

Source: `library/separation.click`, `import click::separation;`.

Law names identify their conclusion: `separate_*` establishes resource separation,
`contains_*` establishes containment, and `viewable_*` establishes viewability.
`distinct_elements` establishes element-address inequality.

### `separation::separate_restrict`

```click
theorem separate_restrict(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b);
}
```

**Meaning:** Contained parts of separate parents are separate. Import
`click::separation` and apply the theorem with the three explicit premises.
`Resource` arguments are descriptors and grant no ownership. This named axiom
is backed by a trusted kernel constructor; application does not search memory
history or discover containment facts.

**Verified use:** [`mdtests/resource_theorem_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/resource_theorem_parameters.md).

### `separation::viewable_restrict`

```click
theorem viewable_restrict(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(A, B);
    ensures viewable(B);
}
```

**Meaning:** A contained part of a viewable resource is viewable at the same
point. This applies to arbitrary resource descriptors, including named
resources and separating conjunctions. For memory,
`viewable(memory(p[a..b]))` is the same fact as `viewable(p[a..b])`.
The axiom grants no ownership and discovers neither containment nor history
paths; both premises are explicit.

**Verified use:** `mdtests/viewable_restrict_memory.md` and
`mdtests/viewable_restrict_resources.md`.

### `separation::viewable_offset_nonnull`

```click
axiom viewable_offset_nonnull<T>(p: T*, lo: uint64, hi: uint64, k: uint64) {
    requires viewable(memory(p[lo..hi]));
    requires lo < hi;
    requires lo <= k;
    requires k <= hi;
    ensures &p[k] != 0;
}
```

**Axiom:** trusted, not proved. C11 6.3.2.3p3 makes a null pointer unequal to
every pointer to an object. A nonempty viewable range `p[lo..hi]` lies in a
live object, and every element address `&p[k]` from `&p[lo]` through
`&p[hi]`, one past the range's end, points into or just past that object
(C11 6.5.6p8, 6.5.9p6), so none is null. An empty range states nothing:
`lo < hi` is required, as C allows a null pointer with a zero length. With
`k` equal to `0`, `&p[0]` is `p` itself, so a view of `p[0..n]` with `0 < n`
gives `p != 0`. The premises are explicit; the axiom grants no access and
searches for no range.

**Verified use:** `mdtests/a_pointer_inside_a_viewed_range_is_not_null.md`.

### `separation::contains_joined_ranges`

Two ordered adjacent ranges on the same pointer cover their combined interval.
This theorem describes the ranges and grants no memory permission.

```click
theorem contains_joined_ranges<T, I>(p: T*, lo: I, mid: I, hi: I) {
    requires lo <= mid;
    requires mid <= hi;
    ensures contains(memory(p[lo..mid]) * memory(p[mid..hi]), memory(p[lo..hi]));
}
```

### Separating conjunction laws

`A * B` is a resource descriptor for separating conjunction; `separation::emp`
is the empty descriptor. Neither grants ownership. The following named axioms
construct their conclusions from exactly the written premises, without opening
resource definitions or discovering containment paths.

| Theorem | Required premises | Conclusion |
| --- | --- | --- |
| `contains_refl(A)` | none | `contains(A, A)` |
| `contains_trans(A, B, C)` | `contains(A, B)`; `contains(B, C)` | `contains(A, C)` |
| `contains_left(A, B)` | none | `contains(A * B, A)` |
| `contains_right(A, B)` | none | `contains(A * B, B)` |
| `separate_symm(A, B)` | `separate(A, B)` | `separate(B, A)` |
| `separate_star(A, B, C)` | `separate(A, C)`; `separate(B, C)` | `separate(A * B, C)` |
| `separate_emp(A)` | none | `separate(separation::emp, A)` |

Import `click::separation`; each theorem above is in the `separation::`
namespace. All parameters have type `Resource`. There is no rule deriving
separation between the two operands merely from writing their conjunction.
For example, `A * A` retains two occurrences and is not identified with `A`.
Use `separate_restrict` to pass separation from a containing resource to a selected part.

**Checked examples:** `mdtests/separation_conjunction.md` and
`mdtests/separation_conjunction_missing_premise.md`.

### `separation::contains_refl`

```click
theorem contains_refl(A: Resource) { ensures contains(A, A); }
```

### `separation::contains_trans`

```click
theorem contains_trans(A: Resource, B: Resource, C: Resource) {
    requires contains(A, B);
    requires contains(B, C);
    ensures contains(A, C);
}
```

### `separation::contains_left`

```click
theorem contains_left(A: Resource, B: Resource) { ensures contains(A * B, A); }
```

### `separation::contains_right`

```click
theorem contains_right(A: Resource, B: Resource) { ensures contains(A * B, B); }
```

### `separation::separate_symm`

```click
theorem separate_symm(A: Resource, B: Resource) {
    requires separate(A, B);
    ensures separate(B, A);
}
```

### `separation::separate_star`

```click
theorem separate_star(A: Resource, B: Resource, C: Resource) {
    requires separate(A, C);
    requires separate(B, C);
    ensures separate(A * B, C);
}
```

### `separation::separate_emp`

```click
theorem separate_emp(A: Resource) { ensures separate(separation::emp, A); }
```

### `separation::separate_elements`

```click
theorem separate_elements<T, I>(p: T*, i: I, j: I) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j]));
}
```

**Meaning:** Unequal indices of one typed array describe separate complete
elements. Both indices have the same inferred type `I`: `int32`, `int64`, or
`uint64`. Signed indices retain signed offsets, including negative offsets;
no unsigned conversion is inserted. The inferred `T` supplies the physical
storage width, including struct padding. Apply with the explicit disequality
premise. The law constructs two element descriptors directly, without enumerating
an interval or inspecting memory history. These are logical resource descriptors;
the law grants no ownership or permission to read or write either element.
Executable pointer arithmetic and accesses retain their normal definedness checks.

The premise is the disequality of the index values at type `I`. For an
`int32` index `m - 1` that is `((m - 1) as int32) != 0`, not the
mathematical Integer fact `m - 1 != 0`, which is a
different proposition. State the word fact with `have ((m - 1) as int32) != 0 by
close();`, which `close()` proves from the Integer fact where the facts keep
`m - 1` in range, and cite `defined(m - 1)` for the argument expression
([`separation_elements_index_word_from_an_integer_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_index_word_from_an_integer_fact.md)).

**Verified use:** [`mdtests/separation_elements.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements.md) and [`mdtests/separation_elements_types.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_types.md). Signed indices and preservation are checked by [`mdtests/separation_elements_signed.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_signed.md) and [`mdtests/separation_elements_signed_store.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_signed_store.md).


### `separation::distinct_elements`

```click
theorem distinct_elements<T, I>(p: T*, i: I, j: I) {
    requires i != j;
    ensures &p[i] != &p[j];
}
```

**Meaning:** Unequal indices of one typed array give unequal element
addresses. Like `separation::separate_elements`, both indices have the same inferred
type `I` (`int32`, `int64`, or `uint64`), the addresses are the exact scaled
offsets `p + i * sizeof(T)` and `p + j * sizeof(T)`, and the premise is the
disequality of the index values at type `I`, such as
`((m - 1) as int32) != 0` or `j != 0u64`. The law states only the address
disequality; it grants no ownership and checks no pointer arithmetic.
`close()` applies it to a goal `&q[j] != &q[0]` after proving the index
disequality. Expansion states the premise with `have` before `apply`
([tactics](../tactics/index.md#arithmetic-with-selected-premises)).

**Verified use:** [`mdtests/solve_proves_element_addresses_distinct_from_their_indices.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_element_addresses_distinct_from_their_indices.md) applies it explicitly and through `close()`, and [`mdtests/solve_proves_element_addresses_distinct_at_each_index_type.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_element_addresses_distinct_at_each_index_type.md) at `uint64` and `int64` indices; [`mdtests/solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.md) refuses equal-possible indices.
### `separation::contains_subrange`

```click
theorem contains_subrange<T, I>(p: T*, lo: I, hi: I, inner_lo: I, inner_hi: I) {
    requires lo <= inner_lo;
    requires inner_lo <= inner_hi;
    requires inner_hi <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[inner_lo..inner_hi]));
}
```

**Meaning:** Nested element intervals describe contained resources. Index type
`I` is `int32` or `uint64`; all four bounds have that same type. Bounds are in
elements of the inferred type `T`, not bytes. Both descriptors retain the
same pointer origin and element width. The law grants no ownership or read
permission. It constructs the containment implication directly, without
searching facts, enumerating elements, or traversing memory history.
Applications supply all three bound premises explicitly. Empty inner intervals
are permitted. Memory access still requires its usual validity conditions. Separation
alone grants no physical-access validity.

**Verified use:** [`mdtests/generic_pointer_theorem_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/generic_pointer_theorem_parameters.md) and [`mdtests/generic_pointer_struct_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/generic_pointer_struct_parameters.md), including padded structs and struct-pointer elements. [`mdtests/separation_subrange_supports_wide_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_subrange_supports_wide_bounds.md) covers unsigned 64-bit bounds.

### `separation::contains_element`

```click
theorem contains_element<T, I>(p: T*, lo: I, hi: I, i: I) {
    requires lo <= i;
    requires i < hi;
    ensures contains(memory(p[lo..hi]), memory(p[i]));
}
```

**Meaning:** An explicitly bounded index denotes a complete element inside its
interval. `I` is `int32` or `uint64`. The upper endpoint is exclusive. The rule
constructs the selected element address directly, preserving the pointer's
carrier and the inferred element width; it does not form a wrapping `i + 1`
endpoint, inspect memory, or search facts. It grants no ownership.

**Verified use:** [`mdtests/separation_element_contains_the_selected_cell.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_element_contains_the_selected_cell.md).

### `separation::contains_rebase`

```click
theorem contains_rebase<T, I>(p: T*, lo: I, hi: I) {
    requires 0 <= to_integer(lo);
    requires lo <= hi;
    ensures contains(memory(p[lo..hi]), memory((p + lo)[0..hi-lo]));
}
```

**Meaning:** The selected interval contains the same interval expressed relative
to its first element. `I` is `int32` or `uint64`; the nonnegative ordered bounds
make `hi-lo` exact. Both descriptors retain the pointer's provenance and the
width of `T`. The rule grants no ownership or read permission and searches no
facts or memory history. Pointer arithmetic and resource expressions retain
their usual evaluation obligations.

**Verified use:** [`mdtests/separation_rebase.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_rebase.md).

## Namespace and extension rules

Library functions, predicates and theorems have qualified names, such as
`click::integer::multiply_add`, so a user declaration may share a library
declaration's bare name; the file then writes the library's by its path. A
selective import of a name the file also declares is refused. Library types,
constructors and resources keep bare names, which a user definition can't
redefine. A C function contract can have the same name as a library pure
function when no user Click definition creates a conflict.

To add a public symbol:

1. Add its declaration to the `library/` module for its topic.
2. Add a focused mdtest that uses it from an ordinary sidecar.
3. Add its semantic entry here; the inventory and exact-declaration checks fail
   until this page agrees with the source.
4. Add general prover or kernel support only when the definition exposes a
   reusable reasoning gap. Don't hard-code a domain-specific library name into
   the kernel merely because it is useful.

### `separation::separate_adjacent_ranges`

```click
theorem separate_adjacent_ranges<T, I>(p: T*, lo: I, mid: I, hi: I) {
    requires lo <= mid;
    requires mid <= hi;
    ensures separate(memory(p[lo..mid]), memory(p[mid..hi]));
}
```

**Meaning:** Ordered adjacent half-open intervals of one typed array are separate.
Either interval may be empty. The bounds share one index type (`int32` or
`uint64`); descriptors use exact element coordinates, without endpoint
subtraction or modular byte arithmetic. The law grants no ownership or access
permission. Application requires both explicit ordering premises and does not
inspect memory history or search for ranges.

**Verified use:** [`mdtests/separation_adjacent_ranges.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_adjacent_ranges.md).

### `integer::lt_le`

```click
theorem lt_le(a: Integer, b: Integer) {
    requires a < b;
    ensures a <= b by {
        have a + 1 <= b by {
            apply(integer::lt_step_le(a, b));
        }
        have a <= a + 1 by { close(); }
        apply(integer::le_transitive(a, a + 1, b));
    }
}
```

### `integer::multiply_associative`

```click
axiom multiply_associative(a: Integer, b: Integer, c: Integer) {
    ensures (a * b) * c == a * (b * c);
}
```

### `integer::multiply_add_left`

```click
theorem multiply_add_left(a: Integer, b: Integer, c: Integer) {
    ensures a * (b + c) == a * b + a * c by {
        apply(integer::multiply_commutative(a, b + c));
        apply(integer::multiply_add(b, c, a));
        apply(integer::multiply_commutative(b, a));
        apply(integer::multiply_commutative(c, a));
        close();
    }
}
```

### `integer::negate_as_product`

```click
theorem negate_as_product(a: Integer) {
    ensures -a == -1 * a by {
        apply(integer::multiply_negate(a, 1));
        apply(integer::multiply_commutative(-1, a));
        have a * 1 == a by close();
        close();
    }
}
```

### `integer::multiply_swap_front`

```click
theorem multiply_swap_front(a: Integer, b: Integer, c: Integer) {
    ensures a * (b * c) == b * (a * c) by {
        apply(integer::multiply_associative(a, b, c));
        apply(integer::multiply_commutative(a, b));
        apply(integer::multiply_associative(b, a, c));
        close();
    }
}
```

### `integer::nonnegative_quotient_from_remainder`

```click
theorem nonnegative_quotient_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires 0 <= r;
    requires r <= d - 1;
    requires n == q * d + r;
    ensures truncating_quotient(n, d) == q by {
        have q * d + 0 <= q * d + r by {
            apply(integer::add_le(q * d, q * d, 0, r));
        }
        have q * d == q * d + 0 by close();
        have q * d <= n by {
            apply(integer::le_substitute(q * d + 0, q * d + r, q * d, n));
        }
        have q <= truncating_quotient(n, d) by {
            apply(integer::positive_divisor_quotient_lower(n, d, q));
        }
        have q * d + r <= q * d + (d - 1) by {
            apply(integer::add_le(q * d, q * d, r, d - 1));
        }
        have n <= q * d + (d - 1) by {
            apply(integer::le_substitute(q * d + r, q * d + (d - 1), n, q * d + (d - 1)));
        }
        have truncating_quotient(n, d) <= q by {
            apply(integer::positive_divisor_quotient_upper_rounded(n, d, q));
        }
        apply(integer::le_antisymmetric(truncating_quotient(n, d), q));
    }
}
```

### `integer::uint32_less_than_divisor_implies_remainder_is_value`

```click
theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by {
        if divisor != 0u32 {
            have 0 <= to_integer(value) by close();
            have to_integer(value) + 1 <= to_integer(divisor) by {
                apply(integer::lt_step_le(to_integer(value), to_integer(divisor)));
            }
            have 0 + 1 <= to_integer(divisor) by {
                have 0 + 1 <= to_integer(value) + 1 by {
                    apply(integer::add_right_order(0, to_integer(value), 1));
                }
                apply(integer::le_transitive(0 + 1, to_integer(value) + 1, to_integer(divisor)));
            }
            have 1 <= to_integer(divisor) by close();
            have 0 < to_integer(divisor) by {
                apply(integer::step_le_lt(0, to_integer(divisor)));
            }
            have to_integer(divisor) != 0 by close();
            have to_integer(value) <= to_integer(divisor) - 1 by {
                apply(integer::lt_le_predecessor(to_integer(value), to_integer(divisor)));
            }
            have to_integer(value) == 0 * to_integer(divisor) + to_integer(value) by close();
            apply(integer::nonnegative_quotient_from_remainder(to_integer(value), to_integer(divisor), 0, to_integer(value)));
            apply(integer::truncation_identity(to_integer(value), to_integer(divisor)));
            apply(integer::uint32_remainder_to_integer(value, divisor));
            have to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)) by {
                have truncating_remainder(to_integer(value), to_integer(divisor)) == 0 * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) by close();
                rewrite(truncating_remainder(to_integer(value), to_integer(divisor)), 0 * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)));
                rewrite(0, truncating_quotient(to_integer(value), to_integer(divisor)));
                close();
            }
            have to_integer(value % divisor) == to_integer(value) by {
                rewrite(to_integer(value % divisor), truncating_remainder(to_integer(value), to_integer(divisor)));
                close();
            }
            close();
        } else {
            have divisor == 0u32 by close();
            have to_integer(divisor) == 0 by close();
            have to_integer(value) < 0 by {
                rewrite(0, to_integer(divisor));
                close();
            }
            have 0 <= to_integer(value) by close();
            contradiction(to_integer(value) < 0);
        }
    }
}
```

A dividend below its unsigned divisor is unchanged by reduction. The strict
unsigned premise excludes a zero divisor; a nonzero divisor or a non-strict
bound alone is insufficient. Values above the signed sign bit retain their
unsigned meaning.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::nonnegative_quotient_shift`

```click
theorem nonnegative_quotient_shift(x: Integer, d: Integer, k: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= x;
    requires 0 <= k;
    ensures truncating_quotient(x + d * k, d) == truncating_quotient(x, d) + k by {
        have 0 <= d by { apply(integer::le_transitive(0, 1, d)); }
        have 0 * d <= k * d by {
            apply(integer::multiply_order_nonnegative(0, k, d));
        }
        have 0 * d == 0 by close();
        have d * k == k * d by { apply(integer::multiply_commutative(d, k)); }
        have 0 <= d * k by {
            apply(integer::le_substitute(0 * d, k * d, 0, d * k));
        }
        have 0 + 0 <= x + d * k by {
            apply(integer::add_le(0, x, 0, d * k));
        }
        have 0 + 0 == 0 by close();
        have 0 <= x + d * k by close();
        have x == truncating_quotient(x, d) * d + truncating_remainder(x, d) by {
            apply(integer::truncation_identity(x, d));
        }
        have 0 <= truncating_remainder(x, d) by {
            apply(integer::nonnegative_dividend_remainder(x, d));
        }
        have 0 < d by { apply(integer::step_le_lt(0, d)); }
        have truncating_remainder(x, d) <= d - 1 by {
            apply(integer::positive_divisor_remainder_upper(x, d));
        }
        have x + d * k == (truncating_quotient(x, d) * d + truncating_remainder(x, d)) + d * k by {
            apply(integer::equal_add(x, truncating_quotient(x, d) * d + truncating_remainder(x, d), d * k, d * k));
        }
        have (truncating_quotient(x, d) + k) * d == truncating_quotient(x, d) * d + k * d by {
            apply(integer::multiply_add(truncating_quotient(x, d), k, d));
        }
        have (truncating_quotient(x, d) * d + truncating_remainder(x, d)) + d * k == (truncating_quotient(x, d) + k) * d + truncating_remainder(x, d) by {
            rewrite((truncating_quotient(x, d) + k) * d, truncating_quotient(x, d) * d + k * d);
            rewrite(d * k, k * d);
            close();
        }
        have x + d * k == (truncating_quotient(x, d) + k) * d + truncating_remainder(x, d) by close();
        apply(integer::nonnegative_quotient_from_remainder(x + d * k, d, truncating_quotient(x, d) + k, truncating_remainder(x, d)));
    }
}
```

### Aligned address word laws

These unsigned equations use explicit `uint64` casts for wrapping arithmetic.
Alignment weakening and masked tags use proved helpers; the elementary word
and scalar-pointer offset laws are trusted axioms. Pointer offsets retain their
element width and either an `int32` or `int64` index.

### `integer::uint64_and_commute`

```click
axiom uint64_and_commute(a: uint64, b: uint64) {
    ensures (a & b) == (b & a);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_and_associate`

```click
axiom uint64_and_associate(a: uint64, b: uint64, c: uint64) {
    ensures ((a & b) & c) == (a & (b & c));
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_or_commute`

```click
axiom uint64_or_commute(a: uint64, b: uint64) {
    ensures (a | b) == (b | a);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_and_or`

```click
axiom uint64_and_or(a: uint64, b: uint64, mask: uint64) {
    ensures ((a | b) & mask) == ((a & mask) | (b & mask));
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_and_zero`

```click
theorem uint64_and_zero(a: uint64) {
    ensures (a & 0u64) == 0u64 by close();
}
```

### `integer::uint64_or_zero`

```click
theorem uint64_or_zero(a: uint64) {
    ensures (a | 0u64) == a by close();
}
```

### `integer::uint64_or_disjoint`

```click
axiom uint64_or_disjoint(a: uint64, b: uint64) {
    requires (a & b) == 0u64;
    ensures (a | b) == ((a + b) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_mask_add_low`

```click
axiom uint64_mask_add_low(base: uint64, tag: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (base & mask) == 0u64;
    ensures ((base + tag) & mask) == (tag & mask);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_mask_add_high`

```click
axiom uint64_mask_add_high(base: uint64, tag: uint64, mask: uint64) {
    requires ((~mask) & ((~mask) + 1u64)) == 0u64;
    requires (base & (~mask)) == 0u64;
    ensures ((base + tag) & mask) == ((base + (tag & mask)) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_mask_multiple`

```click
axiom uint64_mask_multiple(value: uint64, factor: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (factor & mask) == 0u64;
    ensures ((value * factor) & mask) == 0u64;
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_mask_keep`

```click
axiom uint64_mask_keep(base: uint64, mask: uint64) {
    requires (base & (~mask)) == 0u64;
    ensures (base & mask) == base;
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_mask_add_clear`

```click
axiom uint64_mask_add_clear(base: uint64, tag: uint64, mask: uint64) {
    requires ((~mask) & ((~mask) + 1u64)) == 0u64;
    requires (base & (~mask)) == 0u64;
    requires (tag & mask) == 0u64;
    ensures ((base + tag) & mask) == base;
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_add_distinct`

```click
axiom uint64_add_distinct(base: uint64, a: uint64, b: uint64) {
    requires a != b;
    ensures ((base + a) as uint64) != ((base + b) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_add_subtract_cancel`

```click
axiom uint64_add_subtract_cancel(a: uint64, b: uint64) {
    ensures ((((a + b) as uint64) - a) as uint64) == b;
}
```

**Axiom:** trusted, not proved. Wrapping addition and subtraction cancel for every pair of words.

### `integer::uint64_or_add_low`

```click
axiom uint64_or_add_low(base: uint64, tag: uint64, bits: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (base & mask) == 0u64;
    requires (bits & mask) == bits;
    ensures ((base + tag) | bits) == ((base + (tag | bits)) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_mask_subset`

```click
theorem uint64_mask_subset(base: uint64, large: uint64, small: uint64) {
    requires (base & large) == 0u64;
    requires (large & small) == small;
    ensures (base & small) == 0u64 by {
        apply(integer::uint64_and_associate(base, large, small));
        apply(integer::uint64_and_commute(0u64, small));
        rewrite(small, large & small);
        rewrite(base & (large & small), (base & large) & small);
        rewrite(base & large, 0u64);
        rewrite(0u64 & small, small & 0u64);
        close();
    }
}
```

### `integer::uint64_or_masked`

```click
theorem uint64_or_masked(base: uint64, tag: uint64, mask: uint64) {
    requires (base & mask) == 0u64;
    ensures (base | (tag & mask)) == ((base + (tag & mask)) as uint64) by {
        have (base & (tag & mask)) == 0u64 by {
            apply(integer::uint64_and_commute(tag, mask));
            apply(integer::uint64_and_associate(base, mask, tag));
            apply(integer::uint64_and_commute(0u64, tag));
            rewrite(tag & mask, mask & tag);
            rewrite(base & (mask & tag), (base & mask) & tag);
            rewrite(base & mask, 0u64);
            rewrite(0u64 & tag, tag & 0u64);
            close();
        }
        apply(integer::uint64_or_disjoint(base, tag & mask));
    }
}
```

### `integer::uint8_pointer_add_address_int32`

```click
axiom uint8_pointer_add_address_int32(p: uint8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint8_pointer_add_address_int64`

```click
axiom uint8_pointer_add_address_int64(p: uint8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint8_pointer_add_address_uint64`

```click
axiom uint8_pointer_add_address_uint64(p: uint8*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 1u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::int8_pointer_add_address_int32`

```click
axiom int8_pointer_add_address_int32(p: int8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int8_pointer_add_address_int64`

```click
axiom int8_pointer_add_address_int64(p: int8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int8_pointer_add_address_uint64`

```click
axiom int8_pointer_add_address_uint64(p: int8*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 1u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::uint16_pointer_add_address_int32`

```click
axiom uint16_pointer_add_address_int32(p: uint16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint16_pointer_add_address_int64`

```click
axiom uint16_pointer_add_address_int64(p: uint16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint16_pointer_add_address_uint64`

```click
axiom uint16_pointer_add_address_uint64(p: uint16*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 2u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::int16_pointer_add_address_int32`

```click
axiom int16_pointer_add_address_int32(p: int16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int16_pointer_add_address_int64`

```click
axiom int16_pointer_add_address_int64(p: int16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int16_pointer_add_address_uint64`

```click
axiom int16_pointer_add_address_uint64(p: int16*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 2u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::uint32_pointer_add_address_int32`

```click
axiom uint32_pointer_add_address_int32(p: uint32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint32_pointer_add_address_int64`

```click
axiom uint32_pointer_add_address_int64(p: uint32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint32_pointer_add_address_uint64`

```click
axiom uint32_pointer_add_address_uint64(p: uint32*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::int32_pointer_add_address_int32`

```click
axiom int32_pointer_add_address_int32(p: int32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int32_pointer_add_address_int64`

```click
axiom int32_pointer_add_address_int64(p: int32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int32_pointer_add_address_uint64`

```click
axiom int32_pointer_add_address_uint64(p: int32*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::uint64_pointer_add_address_int32`

```click
axiom uint64_pointer_add_address_int32(p: uint64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_pointer_add_address_int64`

```click
axiom uint64_pointer_add_address_int64(p: uint64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::uint64_pointer_add_address_uint64`

```click
axiom uint64_pointer_add_address_uint64(p: uint64*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::int64_pointer_add_address_int32`

```click
axiom int64_pointer_add_address_int32(p: int64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int64_pointer_add_address_int64`

```click
axiom int64_pointer_add_address_int64(p: int64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::int64_pointer_add_address_uint64`

```click
axiom int64_pointer_add_address_uint64(p: int64*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::float32_pointer_add_address_int32`

```click
axiom float32_pointer_add_address_int32(p: float*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::float32_pointer_add_address_int64`

```click
axiom float32_pointer_add_address_int64(p: float*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::float32_pointer_add_address_uint64`

```click
axiom float32_pointer_add_address_uint64(p: float*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 4u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::float64_pointer_add_address_int32`

```click
axiom float64_pointer_add_address_int32(p: double*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::float64_pointer_add_address_int64`

```click
axiom float64_pointer_add_address_int64(p: double*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved.

### `integer::float64_pointer_add_address_uint64`

```click
axiom float64_pointer_add_address_uint64(p: double*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 8u64) as uint64);
}
```

**Axiom:** trusted, not proved. A `size_t` index such as `p + n` with `size_t n`.

### `integer::nonnegative_remainder_from_reconstruction`

Recover a nonnegative dividend's remainder from a reconstruction with a
positive divisor and an explicit remainder range. This is a proved helper for
transporting a bounded residue through scalar addition.

```click
theorem nonnegative_remainder_from_reconstruction(n: Integer, d: Integer, q: Integer, r: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires 0 <= r;
    requires r <= d - 1;
    requires n == q * d + r;
    ensures truncating_remainder(n, d) == r by {
        apply(integer::nonnegative_quotient_from_remainder(n, d, q, r));
        apply(integer::truncation_identity(n, d));
        have n == q * d + truncating_remainder(n, d) by close();
        have n == truncating_remainder(n, d) + q * d by {
            apply(integer::sum_commute(n, q * d, truncating_remainder(n, d)));
        }
        have n == r + q * d by {
            apply(integer::sum_commute(n, q * d, r));
        }
        apply(integer::sum_difference(n, truncating_remainder(n, d), q * d));
        apply(integer::sum_difference(n, r, q * d));
        close();
    }
}
```

**Verified use:** [`signed_interval_remainder_reconstruction.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_interval_remainder_reconstruction.md).

### `integer::uint8_pointer_translate_int32`

```click
axiom uint8_pointer_translate_int32(p: uint8*, q: uint8*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint8_pointer_add_associate_int32`

```click
theorem uint8_pointer_add_associate_int32(p: uint8*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint8_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint8_pointer_translate_uint64`

```click
axiom uint8_pointer_translate_uint64(p: uint8*, q: uint8*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint8_pointer_add_associate_uint64`

```click
theorem uint8_pointer_add_associate_uint64(p: uint8*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint8_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int8_pointer_translate_int32`

```click
axiom int8_pointer_translate_int32(p: int8*, q: int8*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int8_pointer_add_associate_int32`

```click
theorem int8_pointer_add_associate_int32(p: int8*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int8_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int8_pointer_translate_uint64`

```click
axiom int8_pointer_translate_uint64(p: int8*, q: int8*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int8_pointer_add_associate_uint64`

```click
theorem int8_pointer_add_associate_uint64(p: int8*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int8_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint16_pointer_translate_int32`

```click
axiom uint16_pointer_translate_int32(p: uint16*, q: uint16*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint16_pointer_add_associate_int32`

```click
theorem uint16_pointer_add_associate_int32(p: uint16*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint16_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint16_pointer_translate_uint64`

```click
axiom uint16_pointer_translate_uint64(p: uint16*, q: uint16*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint16_pointer_add_associate_uint64`

```click
theorem uint16_pointer_add_associate_uint64(p: uint16*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint16_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int16_pointer_translate_int32`

```click
axiom int16_pointer_translate_int32(p: int16*, q: int16*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int16_pointer_add_associate_int32`

```click
theorem int16_pointer_add_associate_int32(p: int16*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int16_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int16_pointer_translate_uint64`

```click
axiom int16_pointer_translate_uint64(p: int16*, q: int16*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int16_pointer_add_associate_uint64`

```click
theorem int16_pointer_add_associate_uint64(p: int16*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int16_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint32_pointer_translate_int32`

```click
axiom uint32_pointer_translate_int32(p: uint32*, q: uint32*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint32_pointer_add_associate_int32`

```click
theorem uint32_pointer_add_associate_int32(p: uint32*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint32_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint32_pointer_translate_uint64`

```click
axiom uint32_pointer_translate_uint64(p: uint32*, q: uint32*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint32_pointer_add_associate_uint64`

```click
theorem uint32_pointer_add_associate_uint64(p: uint32*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int32_pointer_translate_int32`

```click
axiom int32_pointer_translate_int32(p: int32*, q: int32*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int32_pointer_add_associate_int32`

```click
theorem int32_pointer_add_associate_int32(p: int32*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int32_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int32_pointer_translate_uint64`

```click
axiom int32_pointer_translate_uint64(p: int32*, q: int32*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int32_pointer_add_associate_uint64`

```click
theorem int32_pointer_add_associate_uint64(p: int32*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint64_pointer_translate_int32`

```click
axiom uint64_pointer_translate_int32(p: uint64*, q: uint64*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint64_pointer_add_associate_int32`

```click
theorem uint64_pointer_add_associate_int32(p: uint64*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint64_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint64_pointer_translate_uint64`

```click
axiom uint64_pointer_translate_uint64(p: uint64*, q: uint64*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::uint64_pointer_add_associate_uint64`

```click
theorem uint64_pointer_add_associate_uint64(p: uint64*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int64_pointer_translate_int32`

```click
axiom int64_pointer_translate_int32(p: int64*, q: int64*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int64_pointer_add_associate_int32`

```click
theorem int64_pointer_add_associate_int32(p: int64*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int64_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int64_pointer_translate_uint64`

```click
axiom int64_pointer_translate_uint64(p: int64*, q: int64*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::int64_pointer_add_associate_uint64`

```click
theorem int64_pointer_add_associate_uint64(p: int64*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float32_pointer_translate_int32`

```click
axiom float32_pointer_translate_int32(p: float*, q: float*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float32_pointer_add_associate_int32`

```click
theorem float32_pointer_add_associate_int32(p: float*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float32_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float32_pointer_translate_uint64`

```click
axiom float32_pointer_translate_uint64(p: float*, q: float*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float32_pointer_add_associate_uint64`

```click
theorem float32_pointer_add_associate_uint64(p: float*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float64_pointer_translate_int32`

```click
axiom float64_pointer_translate_int32(p: double*, q: double*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float64_pointer_add_associate_int32`

```click
theorem float64_pointer_add_associate_int32(p: double*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float64_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float64_pointer_translate_uint64`

```click
axiom float64_pointer_translate_uint64(p: double*, q: double*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}
```

**Axiom:** trusted, not proved; both the pointer relation and exact Integer displacement equation are required.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

### `integer::float64_pointer_add_associate_uint64`

```click
theorem float64_pointer_add_associate_uint64(p: double*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
```

**Proved:** from pointer translation and the corresponding addition observation theorem.

**Verified use:** the scalar-width strict replay matrix in [`pointer_offsets.rs`](https://github.com/clicklang/click/blob/master/src/surface/proof/smart_closures/pointer_offsets.rs); representative named applications in [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

## Floating-point order

[`library/float_order.click`](https://github.com/clicklang/click/blob/master/library/float_order.click) provides
local transitivity laws for IEEE comparisons. The two true premises exclude
NaN from every operand. Infinities and signed zeros obey the same laws.
Use these with an explicitly stated intermediate endpoint.

### `float_order::float32_le_le`

```click
axiom float32_le_le(a: float, b: float, c: float) {
    requires a <= b;
    requires b <= c;
    ensures a <= c;
}
```

### `float_order::float32_le_lt`

```click
axiom float32_le_lt(a: float, b: float, c: float) {
    requires a <= b;
    requires b < c;
    ensures a < c;
}
```

### `float_order::float32_lt_le`

```click
axiom float32_lt_le(a: float, b: float, c: float) {
    requires a < b;
    requires b <= c;
    ensures a < c;
}
```

### `float_order::float64_le_le`

```click
axiom float64_le_le(a: double, b: double, c: double) {
    requires a <= b;
    requires b <= c;
    ensures a <= c;
}
```

### `float_order::float64_le_lt`

```click
axiom float64_le_lt(a: double, b: double, c: double) {
    requires a <= b;
    requires b < c;
    ensures a < c;
}
```

### `float_order::float64_lt_le`

```click
axiom float64_lt_le(a: double, b: double, c: double) {
    requires a < b;
    requires b <= c;
    ensures a < c;
}
```

Rounded addition bounds take two ordered inputs and two finite endpoints. The
endpoint sum and the operand sum round at the precision of the law.

### `float_order::float32_add_lower`

```click
axiom float32_add_lower(x: float, y: float, a: float, b: float) {
    requires x >= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y >= a + b;
}
```

### `float_order::float32_add_upper`

```click
axiom float32_add_upper(x: float, y: float, a: float, b: float) {
    requires x <= a;
    requires y <= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y <= a + b;
}
```

### `float_order::float64_add_lower`

```click
axiom float64_add_lower(x: double, y: double, a: double, b: double) {
    requires x >= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y >= a + b;
}
```

### `float_order::float64_add_upper`

```click
axiom float64_add_upper(x: double, y: double, a: double, b: double) {
    requires x <= a;
    requires y <= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y <= a + b;
}
```

A finite positive factor preserves non-strict float32 bounds through rounded multiplication.

### `float_order::float32_scale_lower`

```click
axiom float32_scale_lower(factor: float, x: float, bound: float) {
    requires x >= bound;
    requires isfinite(factor);
    requires float32_from_bits(0) < factor;
    ensures factor * x >= factor * bound;
}
```

### `float_order::float32_scale_upper`

```click
axiom float32_scale_upper(factor: float, x: float, bound: float) {
    requires x <= bound;
    requires isfinite(factor);
    requires float32_from_bits(0) < factor;
    ensures factor * x <= factor * bound;
}
```
