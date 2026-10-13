# Standard library

The Click standard library is the public Surface Click API loaded from
`stdlib/prelude.click` with every user sidecar. It isn't the Rust crate's
internal `pub` API.

Every declaration below is copied exactly from the prelude and checked by the
documentation gate. The same gate compares declaration names bidirectionally,
so adding, removing, or changing a public symbol requires a matching reference
update.

Pure function calls remain symbolic until explicitly unfolded. Predicates
remain opaque until a proof explicitly unfolds them or applies a theorem that
exposes the needed consequence. Theorems can be applied when their stated
requirements are available. An abstract resource has no body to unfold.

## Mutex acquisition authority

### `mutex_guard`

```click
abstract resource mutex_guard(mutex: void*);
```

**Meaning:** Owns one current acquisition of a modeled mutex. The built-in
resource has exclusive unit ownership, no view, and no memory authority.
Use `owns mutex_guard(mu)` inside a declared-resource body. Folding consumes
the existing guard and unfolding returns it; proving `held(mu)` cannot create
it. Contracts may preserve a direct `owns mutex_guard(mu)` input or a folded
guard-bearing instance. Independently checked helpers can unfold and refold
wrappers, but cannot change mutex protocols. Direct clauses return the entry
acquisition. Named primitive binders and consumed/produced guards remain
unsupported.

**Verified use:** [`mdtests/mutex_guard_resource_body.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_guard_resource_body.md).

## Mutex lifecycle authority

### `mutex_live`

```click
abstract resource mutex_live(mutex: void*);
```

**Meaning:** Owns the lifecycle authority for one initialization of a modeled
mutex. Initialization creates this exclusive unit resource. Locking currently
requires it to be available; destruction consumes it. A previous initialization's
owner cannot authorize operations after reinitialization at the same address.
It supplies neither an acquisition nor memory access, and cannot be viewed or
counted.

Use `owns mutex_live(mu)` directly in a preserving contract or inside an
exclusive declared-resource body. Folding consumes the owner; unfolding returns
it. Preserving helpers retain the entry initialization and cannot change mutex
protocols. Missing authority is reported as `Requires owns mutex_live(mu)`.

Initialization requires owned, aligned storage and reserves it against ordinary
writes until destruction. Synchronous helpers can borrow lifetime permission
through `mutex_use`. Worker transfer, named primitive binders, and lifecycle
`consumes`/`produces` contracts remain unsupported.

Automatic objects containing initialized mutexes cannot leave scope until
those mutexes are destroyed, even when their authority is folded away. This
covers normal and abrupt scope exits. Ambiguous symbolic mutex pointers are
refused conservatively rather than assumed separate from local storage.

**Verified use:** [`mdtests/mutex_live_wrapper.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_live_wrapper.md)
and [`mdtests/mutex_live_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_live_contract.md).

## Borrowed mutex lifetime

### `mutex_use`

```click
abstract resource mutex_use(mutex: void*);
```

**Meaning:** An owned permission to use an initialized mutex while its caller
retains lifecycle responsibility. Use `owns mutex_use(mu);` in a preserving
helper contract. Calls borrow an available `mutex_live(mu)` owner or reborrow
an existing use permission; returning restores that exact source. A helper's
input grants neither lifecycle ownership nor protected-memory access.

The current implementation supports synchronous preserving helpers and nested
calls, including contracts with ordinary owned memory and stable views. It
retains the protocol freeze: initialization, destruction, acquisition, and
release inside these helpers remain unsupported. `views`, quantities, named
primitive binders, consumed/produced use permissions, and worker transfer are
also unsupported. Missing call-site authority is reported as
`Requires owns mutex_use(mu)`.

**Verified use:** [`mdtests/mutex_use_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_use_contract.md)
and [`mdtests/mutex_use_mixed.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_use_mixed.md).

## One-shot publication rights

### `publisher`

```click
abstract resource publisher(flag: void*);
```

**Meaning:** The right to publish one payload through the C11 `atomic_int`
flag at `flag`, written `publisher(flag, P(args))` with the payload's resource
type. `atomic_init(flag, 0)` with `{ payload: P(args) }` creates it in the
modeled-pthread runtime. A release store of a nonzero value consumes it
together with a folded `P(args)`. It is unique per flag, grants no memory
access, and may be transferred to a worker. A second release store is reported
as requiring `owns publisher(flag, P)`.

**Verified use:** [`mdtests/publication_one_shot_handoff.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_one_shot_handoff.md)
and [`mdtests/publication_second_release_store_has_no_publisher.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_second_release_store_has_no_publisher.md).

### `subscriber`

```click
abstract resource subscriber(flag: void*);
```

**Meaning:** The right to receive the payload published through the flag at
`flag`, written `subscriber(flag, P(args))`. An acquire load marks it as read
through the loaded value. The C branch that knows the value is zero keeps the
right, and the branch that knows it is nonzero receives an owned `P(args)` in
its place. It is unique per flag and grants no memory access by itself. Loads
without it receive nothing.

**Verified use:** [`mdtests/publication_one_shot_handoff.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_one_shot_handoff.md)
and [`mdtests/publication_unpublished_branch_does_not_receive.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_unpublished_branch_does_not_receive.md).

## Population authority

### `authority`

```click
abstract resource authority();
```

**Meaning:** `authority(reference(p))` is the exclusive control resource for
one population of the declared resource type `reference(p)`. The empty
population may be established with `fold(authority(reference(p)))` only in the
execution proof that created `p`'s storage. It may be retired with
`unfold(authority(reference(p)))` only when its member count is zero. Its
members may be field-free with private owned memory, observed by their current
`count(...)` and moved by direct authority/member helper contracts. An
ordinary field-free control can package counter memory, authorities, and facts
relating the memory to population counts. Ordinary helper contracts transfer
these controls, concrete members, and checked symbolic groups.

Local families can also have C or integer proof fields. For example,
`authority(ticket(p))` governs separately named `ticket(p)` instances; their
identities and field values remain distinct even when their arguments agree.
`let first = fold(ticket(p), { serial: 1 });` creates one member, and
`unfold(first)` consumes that exact member. Both operations require the matching
owned authority. `count(ticket(p))` observes the population total, not field
values or ownership of individual members. Retirement requires zero members.
A wildcard authority such as `authority(ticket(pool, _))` governs all exact
arguments of that local family. Both aggregate and exact counts include separate
occurrences with equal arguments. Private bodies remain exclusive even when
instances share their family arguments.

Preserving helpers take a named member through ordinary `owns` contracts and
retain its proof fields through explicit postconditions. They can unfold and
restore its private body while the caller keeps the authority control closed;
the same population occurrence stays reserved across the preserving call. A
member alone does not permit observing `count(...)`. Verified helpers can
create or consume named members when their checked input partition supplies the
governing authority. Creation needs an increment bound; consumption needs the
exact owned occurrence. Unary and wildcard imports preserve arbitrary entry
totals and record relative effects without anonymous member rights. Assumed
interfaces may preserve named ownership but cannot perform these lifecycle
effects. Symbolic quantities of heterogeneous named instances remain unsupported.

**Verified use:** [`mdtests/authority_named_field_members.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_named_field_members.md).

**Verified use:** [`mdtests/authority_named_field_private_helper.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_named_field_private_helper.md).

**Verified use:** [`authority_control_wrapper_tracks_memory_and_member_count_through_open_scopes`](https://github.com/clicklang/click/blob/master/src/surface/tests/authority_private_body_tests.rs).

A count and an equal C counter can have different checked term representations.
To transfer increment definedness, explicitly rewrite the count to the counter
using the control's equality and establish the nonnegative bound as needed.
For example, `rewrite(count(item(pool, _)) == pool->checked_out)` can transport
`defined(pool->checked_out + 1)` inside an opened control. Nonnegativity alone
does not establish increment safety: the count can still be `2147483647`.

**Verified use:** [`authority_count_defined_through_control.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_count_defined_through_control.md)
and [`authority_count_defined_at_max_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_count_defined_at_max_rejected.md).

## Allocation authority

### `allocation`

```click
abstract resource allocation(base: int32*, bytes: int32);
```

**Meaning:** Owns the lifetime authority for the heap allocation whose base pointer is `base` and whose extent is `bytes`. The resource is abstract and cannot be unfolded.

**Kind:** abstract resource. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## Natural numbers

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

### `nat_integer_zero`

```click
theorem nat_integer_zero() {
    ensures to_integer(Nat::Zero) == 0;
}
```

### `nat_integer_succ`

```click
theorem nat_integer_succ(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1;
}
```

### `nat_integer_nonnegative`

```click
theorem nat_integer_nonnegative(n: Nat) {
    ensures to_integer(n) >= 0;
}
```

### `nat_integer_round_trip`

```click
theorem nat_integer_round_trip(n: Nat) {
    ensures to_nat(to_integer(n)) == n;
}
```

### `integer_nat_round_trip`

```click
theorem integer_nat_round_trip(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z;
}
```

### `integer_to_nat_zero`

```click
theorem integer_to_nat_zero() {
    ensures to_nat(0) == Nat::Zero;
}
```

### `nat_add`

```click
function nat_add(left: Nat, right: Nat) -> Nat
    decreases left
{
    match left {
        Nat::Zero => right,
        Nat::Succ(previous) => Nat::Succ(nat_add(previous, right)),
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat_add_left_identity`

```click
theorem nat_add_left_identity(n: Nat) {
    ensures nat_add(Nat::Zero, n) == n by {
        unfold(nat_add(Nat::Zero, n));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat_add_succ_left`

```click
theorem nat_add_succ_left(n: Nat, m: Nat) {
    ensures nat_add(Nat::Succ(n), m) == Nat::Succ(nat_add(n, m)) by {
        unfold(nat_add(Nat::Succ(n), m));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat_integer_add`

The ordinary structural addition agrees with exact Integer addition. Its proof
uses Nat induction and explicit, locally checked linear certificates.

```click
theorem nat_integer_add(n: Nat, m: Nat) {
    ensures to_integer(nat_add(n, m)) == to_integer(n) + to_integer(m) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, m));
                apply(nat_integer_zero());
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Zero) == 0 => to_integer(Nat::Zero) == 0;
                    scale 0 by -1 => to_integer(m) == to_integer(Nat::Zero) + to_integer(m);
                    conclusion 1;
                }
            }
            Nat::Succ(previous) => {
                unfold(nat_add(Nat::Succ(previous), m));
                apply(nat_integer_succ(nat_add(previous, m)));
                apply(ih(previous));
                apply(nat_integer_succ(previous));
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(nat_add(previous, m)) + 1 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(nat_add(previous, m)) + 1;
                    premise 1: to_integer(nat_add(previous, m)) == to_integer(previous) + to_integer(m) => to_integer(nat_add(previous, m)) == to_integer(previous) + to_integer(m);
                    premise 2: to_integer(Nat::Succ(previous)) == to_integer(previous) + 1 => to_integer(Nat::Succ(previous)) == to_integer(previous) + 1;
                    add 0, 1 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(previous) + to_integer(m) + 1;
                    scale 2 by -1 => to_integer(previous) + 1 == to_integer(Nat::Succ(previous));
                    add 3, 4 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(Nat::Succ(previous)) + to_integer(m);
                    conclusion 5;
                }
            }
        }
    }
}
```

### `nat_add_right_identity`

```click
theorem nat_add_right_identity(n: Nat) {
    ensures nat_add(n, Nat::Zero) == n by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, Nat::Zero));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), Nat::Zero));
                rewrite(nat_add(previous, Nat::Zero) == previous);
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat_add_succ_right`

```click
theorem nat_add_succ_right(n: Nat, m: Nat) {
    ensures nat_add(n, Nat::Succ(m)) == Nat::Succ(nat_add(n, m)) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, Nat::Succ(m)));
                unfold(nat_add(Nat::Zero, m));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), Nat::Succ(m)));
                unfold(nat_add(Nat::Succ(previous), m));
                rewrite(nat_add(previous, Nat::Succ(m)) == Nat::Succ(nat_add(previous, m)));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat_add_associative`

```click
theorem nat_add_associative(a: Nat, b: Nat, c: Nat) {
    ensures nat_add(nat_add(a, b), c) == nat_add(a, nat_add(b, c)) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, b));
                unfold(nat_add(Nat::Zero, nat_add(b, c)));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                apply(nat_add_succ_left(previous, b));
                rewrite(nat_add(Nat::Succ(previous), b) == Nat::Succ(nat_add(previous, b)));
                apply(nat_add_succ_left(nat_add(previous, b), c));
                rewrite(nat_add(Nat::Succ(nat_add(previous, b)), c)
                    == Nat::Succ(nat_add(nat_add(previous, b), c)));
                apply(nat_add_succ_left(previous, nat_add(b, c)));
                rewrite(nat_add(Nat::Succ(previous), nat_add(b, c))
                    == Nat::Succ(nat_add(previous, nat_add(b, c))));
                rewrite(nat_add(nat_add(previous, b), c) == nat_add(previous, nat_add(b, c)));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat_add_commutative`

```click
theorem nat_add_commutative(a: Nat, b: Nat) {
    ensures nat_add(a, b) == nat_add(b, a) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, b));
                apply(nat_add_right_identity(b));
                rewrite(nat_add(b, Nat::Zero) == b);
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), b));
                apply(nat_add_succ_right(b, previous));
                rewrite(nat_add(b, Nat::Succ(previous)) == Nat::Succ(nat_add(b, previous)));
                rewrite(nat_add(previous, b) == nat_add(b, previous));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).


## Lists

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

### `list_append`

```click
function list_append<T>(xs: List<T>, ys: List<T>) -> List<T>
    decreases xs
{
    match xs {
        List::Nil => ys,
        List::Cons(head, tail) => List<T>::Cons(head, list_append(tail, ys)),
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_contains`

```click
function list_contains<T>(xs: List<T>, value: T) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) =>
            if head == value { 1 } else { list_contains(tail, value) },
    }
}
```

Returns `1` for membership and `0` otherwise, using element equality.
Its checked laws support C scalar, pointer, and algebraic-valued elements,
including nested lists. Comparisons of unknown algebraic values stay symbolic.

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_append_left_identity`

```click
theorem list_append_left_identity<T>(xs: List<T>) {
    ensures list_append(List<T>::Nil, xs) == xs by {
        unfold(list_append(List<T>::Nil, xs));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_append_right_identity`

```click
theorem list_append_right_identity<T>(xs: List<T>) {
    ensures list_append(xs, List<T>::Nil) == xs by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, List<T>::Nil));
                normalize();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                unfold(list_append(List<T>::Cons(head, tail), List<T>::Nil));
                rewrite(list_append(tail, List<T>::Nil) == tail);
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_append_cons`

```click
theorem list_append_cons<T>(head: T, tail: List<T>, ys: List<T>) {
    ensures list_append(List<T>::Cons(head, tail), ys)
        == List<T>::Cons(head, list_append(tail, ys)) by {
        unfold(list_append(List<T>::Cons(head, tail), ys));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_append_associative`

```click
theorem list_append_associative<T>(xs: List<T>, ys: List<T>, zs: List<T>) {
    ensures list_append(list_append(xs, ys), zs)
        == list_append(xs, list_append(ys, zs)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_append(List<T>::Nil, list_append(ys, zs)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                apply(list_append_cons(head, list_append(tail, ys), zs));
                rewrite(list_append(List<T>::Cons(head, list_append(tail, ys)), zs)
                    == List<T>::Cons(head, list_append(list_append(tail, ys), zs)));
                apply(list_append_cons(head, tail, list_append(ys, zs)));
                rewrite(list_append(List<T>::Cons(head, tail), list_append(ys, zs))
                    == List<T>::Cons(head, list_append(tail, list_append(ys, zs))));
                rewrite(list_append(list_append(tail, ys), zs)
                    == list_append(tail, list_append(ys, zs)));
                simp();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_contains_nil`

```click
theorem list_contains_nil<T>(value: T) {
    ensures list_contains(List<T>::Nil, value) == 0 by {
        unfold(list_contains(List<T>::Nil, value));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_contains_cons`

```click
theorem list_contains_cons<T>(head: T, tail: List<T>, value: T) {
    ensures list_contains(List<T>::Cons(head, tail), value)
        == if head == value { 1 } else { list_contains(tail, value) } by {
        unfold(list_contains(List<T>::Cons(head, tail), value));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list_contains_append`

```click
theorem list_contains_append<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) == 1 { 1 } else { list_contains(ys, value) } by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_contains(List<T>::Nil, value));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                if head == value {
                    apply(list_contains_cons(head, list_append(tail, ys), value));
                    rewrite(list_contains(List<T>::Cons(head, list_append(tail, ys)), value)
                        == if head == value { 1 } else { list_contains(list_append(tail, ys), value) });
                    apply(list_contains_cons(head, tail, value));
                    rewrite(list_contains(List<T>::Cons(head, tail), value)
                        == if head == value { 1 } else { list_contains(tail, value) });
                    normalize() using { head == value; }
                } else {
                    apply(list_contains_cons(head, list_append(tail, ys), value));
                    rewrite(list_contains(List<T>::Cons(head, list_append(tail, ys)), value)
                        == if head == value { 1 } else { list_contains(list_append(tail, ys), value) });
                    apply(list_contains_cons(head, tail, value));
                    rewrite(list_contains(List<T>::Cons(head, tail), value)
                        == if head == value { 1 } else { list_contains(tail, value) });
                    rewrite(list_contains(list_append(tail, ys), value)
                        == if list_contains(tail, value) == 1 { 1 } else { list_contains(ys, value) });
                    normalize() using { not(head == value); }
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

`list_length` returns `Nat`, so a length cannot be negative or overflow.
These laws hold for arbitrary element types, including nested lists.

### `list_length`

```click
function list_length<T>(xs: List<T>) -> Nat
    decreases xs
{
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(head, tail) => Nat::Succ(list_length(tail)),
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list_length_nil`

```click
theorem list_length_nil<T>(xs: List<T>) {
    requires xs == List<T>::Nil;
    ensures list_length(xs) == Nat::Zero by {
        rewrite(xs == List<T>::Nil);
        unfold(list_length(List<T>::Nil));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list_length_cons`

```click
theorem list_length_cons<T>(head: T, tail: List<T>) {
    ensures list_length(List<T>::Cons(head, tail)) == Nat::Succ(list_length(tail)) by {
        unfold(list_length(List<T>::Cons(head, tail)));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list_length_append`

```click
theorem list_length_append<T>(xs: List<T>, ys: List<T>) {
    ensures list_length(list_append(xs, ys)) == nat_add(list_length(xs), list_length(ys)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_length(List<T>::Nil));
                unfold(nat_add(Nat::Zero, list_length(ys)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                apply(list_length_cons(head, list_append(tail, ys)));
                rewrite(list_length(List<T>::Cons(head, list_append(tail, ys)))
                    == Nat::Succ(list_length(list_append(tail, ys))));
                apply(list_length_cons(head, tail));
                rewrite(list_length(List<T>::Cons(head, tail)) == Nat::Succ(list_length(tail)));
                apply(nat_add_succ_left(list_length(tail), list_length(ys)));
                rewrite(nat_add(Nat::Succ(list_length(tail)), list_length(ys))
                    == Nat::Succ(nat_add(list_length(tail), list_length(ys))));
                rewrite(list_length(list_append(tail, ys)) == nat_add(list_length(tail), list_length(ys)));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).


## Signed `int32` theorems

### `int32_increment_upper_bound`

```click
theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures value + 1 <= upper;
}
```

**Meaning:** Given its listed requirements, proves `value + 1 <= upper`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_strictly_increases`

```click
theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures value < value + 1;
}
```

**Meaning:** Given its listed requirements, proves `value < value + 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_lower_bound`

```click
theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower <= value + 1;
}
```

**Meaning:** Given its listed requirements, proves `lower <= value + 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_greater_equal_lower_bound`

```click
theorem int32_increment_greater_equal_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 >= lower;
}
```

**Meaning:** Given its listed requirements, proves `value + 1 >= lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_greater_than_lower_bound`

```click
theorem int32_increment_greater_than_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 > lower;
}
```

**Meaning:** Given its listed requirements, proves `value + 1 > lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_preserves_order`

```click
theorem int32_increment_preserves_order(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower + 1 <= value + 1;
}
```

**Meaning:** Given its listed requirements, proves `lower + 1 <= value + 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_less_equal_implies_less_than`

```click
theorem int32_increment_less_equal_implies_less_than(lower: int32, value: int32) {
    requires lower < lower + 1;
    requires lower + 1 <= value;

    ensures lower < value;
}
```

**Meaning:** Given its listed requirements, proves `lower < value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_than_increment_implies_less_equal`

```click
theorem int32_less_than_increment_implies_less_equal(value: int32, upper: int32) {
    requires value < upper + 1;

    ensures value <= upper;
}
```

**Meaning:** Given its listed requirement, proves `value <= upper`. If `upper + 1` wraps, the strict requirement is unsatisfiable, so the implication remains valid.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_positive_is_nonnegative`

```click
theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value;
}
```

**Meaning:** Given its listed requirements, proves `0 <= value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_than_implies_less_equal`

```click
theorem int32_less_than_implies_less_equal(left: int32, right: int32) {
    requires left < right;

    ensures left <= right;
}
```

**Meaning:** Given its listed requirements, proves `left <= right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_than_implies_not_equal`

```click
theorem int32_less_than_implies_not_equal(left: int32, right: int32) {
    requires left < right;

    ensures left != right;
}
```

**Meaning:** Given its listed requirement, proves `left != right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_not_less_than_implies_greater_equal`

```click
theorem int32_not_less_than_implies_greater_equal(left: int32, right: int32) {
    requires not (left < right);

    ensures left >= right;
}
```

**Meaning:** Given its listed requirements, proves `left >= right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_below_max_is_defined`

```click
theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1);
}
```

**Meaning:** Given its listed requirements, proves `defined(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_left_below_max_is_defined`

```click
theorem int32_increment_left_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(1 + value);
}
```

**Meaning:** Given its listed requirements, proves `defined(1 + value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_left_strictly_increases`

```click
theorem int32_increment_left_strictly_increases(value: int32) {
    requires value < 2147483647;

    ensures value < 1 + value;
}
```

**Meaning:** Given its listed requirements, proves `value < 1 + value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_nonnegative_add_within_max_is_defined`

```click
theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires value <= 2147483647 - amount;

    ensures defined(value + amount);
}
```

**Meaning:** Given its listed requirements, proves `defined(value + amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_nonnegative_subtract_within_value_is_defined`

```click
theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount);
}
```

**Meaning:** Given its listed requirements, proves `defined(value - amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_move_one_from_right_to_left_preserves_sum`

```click
theorem int32_move_one_from_right_to_left_preserves_sum(
    total: int32,
    left: int32,
    right: int32
) {
    requires 0 <= left;
    requires 1 <= right;
    requires total == left + right;

    ensures total == (left + 1) + (right - 1);
}
```

**Meaning:** Given its listed requirements, proves `total == (left + 1) + (right - 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_subtract_equal_sum_right_cancels`

```click
theorem int32_subtract_equal_sum_right_cancels(value: int32, left: int32, amount: int32) {
    requires defined(left + amount) and value == left + amount;
    requires defined(value - amount);

    ensures value - amount == left by {
        rewrite(value == left + amount);
        simp();
    }
}
```

**Meaning:** Given its listed requirements, proves `value - amount == left`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_add_defined_by_integer_bounds`

```click
theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right);
}
```

Bounds on the mathematical sum establish that signed C addition does not overflow.
Both bounds are required, including when the final program result is in range.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int32_subtract_defined_by_integer_bounds`

```click
theorem int32_subtract_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) - to_integer(right) >= -2147483648;
    requires to_integer(left) - to_integer(right) <= 2147483647;
    ensures defined(left - right);
}
```

Bounds on the mathematical difference establish that signed C subtraction
does not overflow. It is the subtraction twin of
`int32_add_defined_by_integer_bounds`, and both bounds are likewise required.
When constant bounds on the operands themselves suffice, the checked
`int32_defined` certificate step needs no `to_integer` conversion
([tactics reference](../tactics/index.md)).

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_widened_add_guard_by_integer_bound`

```click
theorem uint32_widened_add_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures ((int64)left + (int64)right) <= 4294967295i64;
}
```

Bounds on unsigned Integer observations imply the widened signed `int64` addition guard used by checked Rust addition. Both operands are widened before addition; their sum always fits `int64`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_add_to_integer`

```click
theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}
```

Unsigned machine addition agrees with mathematical addition when the mathematical sum fits `uint32`. Unsigned definedness alone allows wrapping and cannot establish this equality.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_subtract_to_integer`

```click
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}
```

Unsigned subtraction agrees with Integer subtraction under the native unsigned no-underflow guard. The rule covers the full `uint32` range. Native definedness alone permits wrapping, so it cannot replace the guard.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_nonzero_to_integer`

```click
theorem uint32_nonzero_to_integer(value: uint32) {
 requires value != 0u32;
 ensures to_integer(value) != 0 by {
  apply(uint32_remainder_less_than_divisor(0u32, value)) using { value != 0u32; }
  apply(uint32_less_than_to_integer(0u32 % value, value)) using { 0u32 % value < value; }
  apply(uint32_to_integer_bounds(0u32 % value));
  have 1 <= to_integer(value) by {
   arithmetic() using { 0 <= to_integer(0u32 % value); to_integer(0u32 % value) < to_integer(value); }
  }
  arithmetic_certificate rules {
   premise 0: 1 <= to_integer(value) => 1 <= to_integer(value);
   integer_bound_exclusion bounds [0] => to_integer(value) != 0;
   conclusion 0;
  }
 }
}
```

A checked source proof derives a nonzero Integer observation from a nonzero unsigned machine value. It introduces no additional kernel axiom.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_divide_to_integer`

```click
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}
```

Unsigned division agrees with Integer truncating division when both evaluation domains exclude zero. No overflow bound on the dividend is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_remainder_to_integer`

```click
theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Unsigned remainder agrees with Integer truncating remainder when both evaluation domains exclude zero. Combine this bridge with `uint32_nonzero_to_integer` when a caller supplies only the native guard.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_multiply_to_integer`

```click
theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right);
}
```

Unsigned multiplication agrees with Integer multiplication under the native no-overflow guard. A zero right operand satisfies the guard without division; other operands must fit the unsigned quotient ceiling. Native unsigned definedness alone permits wrapping.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_multiply_guard_by_integer_bound`

```click
theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right;
}
```

A mathematical product bound establishes the native checked-multiplication guard used by Rust. The zero right operand needs no division. Combine this rule with `uint32_multiply_to_integer` to prove an exact product from Integer bounds; bounding the already wrapped machine product is insufficient.

**Verified use:** [`mdtests/integer_uint32_product_bound_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_uint32_product_bound_guard.md).

### `uint64_add_to_integer`

```click
theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}
```

Unsigned addition agrees with Integer addition when the sum fits uint64. Native unsigned definedness alone permits wrapping.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_multiply_to_integer`

```click
theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right);
}
```

Unsigned multiplication agrees with the Integer product when it fits uint64. The explicit product bound excludes wrap.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_subtract_to_integer`

```click
theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}
```

Unsigned subtraction agrees with Integer subtraction when the subtrahend is at most the minuend, excluding underflow.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_divide_to_integer`

```click
theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}
```

Unsigned division agrees with the truncating Integer quotient. Both native and observed nonzero divisor premises are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_remainder_to_integer`

```click
theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Unsigned remainder agrees with the truncating Integer remainder. Both native and observed nonzero divisor premises are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_less_equal_to_integer`

```click
theorem uint64_less_equal_to_integer(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}
```

Native uint64 non-strict order implies exact Integer observation order, including values above the sign bit.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_to_integer_less_equal_implies_less_equal`

```click
theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}
```

Exact Integer observation order implies native uint64 non-strict order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_less_than_to_integer`

```click
theorem uint64_less_than_to_integer(left: uint64, right: uint64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right);
}
```

Native uint64 strict order implies strict order of the exact Integer observations, including values above the sign bit.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_to_integer_less_than_implies_less_than`

```click
theorem uint64_to_integer_less_than_implies_less_than(left: uint64, right: uint64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right;
}
```

Strict order of the exact Integer observations implies native uint64 strict order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_pack_uint16_to_integer`

```click
theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value when both native bounds hold.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_pack_uint16_high_first_to_integer`

```click
theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value with the shifted high field written first. Both native bounds are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_unpack_uint16_low`

```click
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_unpack_uint16_high`

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

### `uint64_pack_uint16_to_integer`

```click
theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value when both native bounds hold.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_less_than_implies_not_greater_equal`

```click
theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right);
}
```

A strict unsigned order excludes the opposite greater-or-equal branch.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_to_integer_equal_implies_equal`

```click
theorem uint64_to_integer_equal_implies_equal(left: uint64, right: uint64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}
```

Equal exact unsigned observations identify the same native value, over the whole 64-bit range. `arithmetic` uses it to conclude a `uint64` equality it proved as an Integer claim.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_less_equal_to_integer`

```click
theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}
```

Preserves native unsigned order in exact Integer observations, including values above the sign bit. The native order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_to_integer_less_equal_implies_less_equal`

```click
theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}
```

Reflects exact Integer observation order into native unsigned order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_to_integer_equal_implies_equal`

```click
theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}
```

Reflects equal exact Integer observations into native unsigned equality. Every
32-bit pattern, including those above the signed sign bit, has one unsigned
Integer value, so the observation is injective.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_less_than_to_integer`

```click
theorem uint32_less_than_to_integer(left: uint32, right: uint32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            apply(uint32_to_integer_less_equal_implies_less_equal(right, left));
            contradiction(left < right);
        } else {
            arithmetic() using { not (to_integer(right) <= to_integer(left)); }
        }
    }
}
```

Preserves strict native unsigned order in exact Integer observations.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_remainder_less_than_divisor`

```click
theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor;
}
```

The unsigned remainder is below its divisor for any dividend. The nonzero divisor premise is essential.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_less_than_divisor_implies_remainder_is_value`

```click
theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value;
}
```

A dividend below its unsigned divisor is unchanged by reduction. The strict
unsigned premise excludes a zero divisor; a nonzero divisor or a non-strict
bound alone is insufficient. Values above the signed sign bit retain their
unsigned meaning.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_to_integer_bounds`

```click
theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; }
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; }
    }
}
```

Proves the full unsigned observation range from native order. This theorem does not distribute observations over wrapping operations.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int32_to_integer_bounds`

```click
theorem int32_to_integer_bounds(value: int32) {
    ensures -2147483648 <= to_integer(value) by {
        have -2147483648 <= value;
        apply(int32_less_equal_to_integer(-2147483648, value)) using { -2147483648 <= value; }
    }
    ensures to_integer(value) <= 2147483647 by {
        have value <= 2147483647;
        apply(int32_less_equal_to_integer(value, 2147483647)) using { value <= 2147483647; }
    }
}
```

Proves the full signed 32-bit observation range from native order. `auto` applies it to an `int32` value whose range its `Integer` claim needs.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_to_integer_bounds`

```click
theorem int64_to_integer_bounds(value: int64) {
    ensures -9223372036854775808 <= to_integer(value) by {
        have -9223372036854775808i64 <= value;
        apply(int64_less_equal_to_integer(-9223372036854775808i64, value)) using { -9223372036854775808i64 <= value; }
    }
    ensures to_integer(value) <= 9223372036854775807 by {
        have value <= 9223372036854775807i64;
        apply(int64_less_equal_to_integer(value, 9223372036854775807i64)) using { value <= 9223372036854775807i64; }
    }
}
```

Proves the full signed 64-bit observation range from native order.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_to_integer_bounds`

```click
theorem uint64_to_integer_bounds(value: uint64) {
    ensures 0 <= to_integer(value) by {
        have 0u64 <= value;
        apply(uint64_less_equal_to_integer(0u64, value)) using { 0u64 <= value; }
    }
    ensures to_integer(value) <= 18446744073709551615 by {
        have value <= 18446744073709551615u64;
        apply(uint64_less_equal_to_integer(value, 18446744073709551615u64)) using { value <= 18446744073709551615u64; }
    }
}
```

Proves the full unsigned 64-bit observation range from native order. `arithmetic` applies it to each `uint64` variable it reads, so a sum bounded only by another `uint64` value is known not to wrap.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int32_add_to_integer`

```click
theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}
```

A defined signed C addition has the same value as mathematical Integer addition.
The definedness premise excludes overflow; the equality is not unconditional.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_add_defined_by_integer_bounds`

```click
theorem int64_add_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) + to_integer(right) >= -9223372036854775808;
    requires to_integer(left) + to_integer(right) <= 9223372036854775807;
    ensures defined(left + right);
}
```

Bounds on the exact mathematical sum establish that signed 64-bit addition is defined. Both bounds are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_subtract_defined_by_integer_bounds`

```click
theorem int64_subtract_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) - to_integer(right) >= -9223372036854775808;
    requires to_integer(left) - to_integer(right) <= 9223372036854775807;
    ensures defined(left - right);
}
```

Bounds on the exact mathematical difference establish that signed 64-bit subtraction is defined. Both bounds are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_to_integer_less_than_implies_less_than`

```click
theorem int64_to_integer_less_than_implies_less_than(left: int64, right: int64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right;
}
```

Strict order of the exact Integer observations implies native signed int64 strict order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_add_to_integer`

```click
theorem int64_add_to_integer(left: int64, right: int64) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}
```

A defined signed 64-bit operation has its exact mathematical Integer value.
The native definedness premise excludes overflow; this law does not establish
that premise or infer any operand range.

**Verified use:** [`mdtests/int64_integer_operation_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/int64_integer_operation_bridges.md).

### `int64_subtract_to_integer`

```click
theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}
```

A defined signed 64-bit operation has its exact mathematical Integer value.
The native definedness premise excludes overflow; this law does not establish
that premise or infer any operand range.

**Verified use:** [`mdtests/int64_integer_operation_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/int64_integer_operation_bridges.md).

### `int32_subtract_to_integer`

```click
theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}
```

A defined signed C subtraction has the same value as mathematical Integer subtraction.
The definedness premise excludes overflow; the equality is not unconditional.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int32_to_integer_equal_implies_equal`

```click
theorem int32_to_integer_equal_implies_equal(left: int32, right: int32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}
```

The signed `int32` observation is injective: equal mathematical observations
identify the same machine value. This bridge needs the exact equality premise;
an order comparison or an observation of a different carrier is insufficient.
It introduces no conversion back to a machine value and needs no overflow
premise. Use it after checked machine-to-`Integer` arithmetic bridges when
restoring a machine-valued invariant.

**Verified use:** [`mdtests/int32_equality_from_integer_observations.md`](https://github.com/clicklang/click/blob/master/mdtests/int32_equality_from_integer_observations.md),
[`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int32_less_equal_to_integer`

```click
theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}
```

A signed C order fact transfers to the exact mathematical observations of the
two operands. The C order premise is required; the bridge does not assume an
order between unrelated machine values.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int32_less_than_to_integer`

```click
theorem int32_less_than_to_integer(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            apply(int32_to_integer_less_equal_implies_less_equal(right, left));
            contradiction(left < right);
        } else {
            arithmetic() using { not (to_integer(right) <= to_integer(left)); }
        }
    }
}
```

A strict signed native comparison transfers to mathematical Integer order,
including when an operand is a narrowed wide value. This is a proof-backed
lemma: it uses the existing non-strict reflection bridge by contraposition,
rather than extending the trusted kernel. A non-strict premise is insufficient.

**Verified use:** [`mdtests/integer_strict_order_observation.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_strict_order_observation.md),
[`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int32_to_integer_less_equal_implies_less_equal`

```click
theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}
```

A proved non-strict order between exact signed observations establishes the native order. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `int64_less_equal_to_integer`

```click
theorem int64_less_equal_to_integer(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}
```

The exact signed mathematical observation preserves native non-strict order. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `int64_less_than_to_integer`

```click
theorem int64_less_than_to_integer(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right);
}
```

Preserves the exact source comparison in signed 64-bit Integer observations, including the signed endpoints. The native comparison premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_greater_equal_to_integer`

```click
theorem int64_greater_equal_to_integer(left: int64, right: int64) {
    requires left >= right;
    ensures to_integer(left) >= to_integer(right);
}
```

Preserves the exact source comparison in signed 64-bit Integer observations, including the signed endpoints. The native comparison premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_to_integer_less_equal_implies_less_equal`

```click
theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}
```

A proved non-strict order between exact signed observations establishes the native order. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `int64_to_integer_equal_implies_equal`

```click
theorem int64_to_integer_equal_implies_equal(left: int64, right: int64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}
```

Equal exact signed observations identify the same native value, including full-width extrema. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `int32_add_nonnegative_right_is_at_least_left`

```click
theorem int32_add_nonnegative_right_is_at_least_left(left: int32, right: int32) {
    requires 0 <= right;
    requires defined(left + right);

    ensures left <= left + right;
}
```

**Meaning:** Given its listed requirements, proves `left <= left + right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_add_nonnegative_left_is_at_least_right`

```click
theorem int32_add_nonnegative_left_is_at_least_right(left: int32, right: int32) {
    requires 0 <= left;
    requires defined(left + right);

    ensures right <= left + right;
}
```

**Meaning:** Given its listed requirements, proves `right <= left + right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_positive_predecessor_is_nonnegative`

```click
theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value - 1;
}
```

**Meaning:** Given its listed requirements, proves `0 <= value - 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_above_one_predecessor_is_at_least_one`

```click
theorem int32_above_one_predecessor_is_at_least_one(value: int32) {
    requires 1 < value;

    ensures value - 1 >= 1;
}
```

**Meaning:** Given its listed requirements, proves `value - 1 >= 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_positive_predecessor_strictly_decreases`

```click
theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures value - 1 < value;
}
```

**Meaning:** Given its listed requirements, proves `value - 1 < value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_positive_predecessor_strictly_decreases`

```click
theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures value - 1u32 < value;
}
```

**Meaning:** Given its listed requirements, proves `value - 1u32 < value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_increment_upper_bound`

```click
theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value + 1u32 <= upper;
}
```

**Meaning:** Given its listed requirements, proves `value + 1u32 <= upper`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_increment_strictly_increases`

```click
theorem uint32_increment_strictly_increases(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value < value + 1u32;
}
```

**Meaning:** Given its listed requirements, proves `value < value + 1u32`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_less_than_implies_positive_difference`

```click
theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0u32 < upper - value;
}
```

**Meaning:** Given its listed requirements, proves `0u32 < upper - value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_difference_decreases_after_increment`

```click
theorem uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures (0u32 - value) + (bound - 1u32) < (0u32 - value) + bound;
}
```

**Meaning:** Given its listed requirements, proves `(0u32 - value) + (bound - 1u32) < (0u32 - value) + bound`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_less_than_less_equal_transitive`

```click
theorem uint32_less_than_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_less_equal_less_than_transitive`

```click
theorem uint32_less_equal_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_less_than_transitive`

```click
theorem uint32_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_less_equal_transitive`

```click
theorem uint32_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}
```

**Meaning:** Given its listed requirements, proves `first <= last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint64_less_than_less_equal_transitive`

```click
theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}
```

Transitivity of unsigned 64-bit order: `first < middle` and `middle <= last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_less_equal_less_than_transitive`

```click
theorem uint64_less_equal_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}
```

Transitivity of unsigned 64-bit order: `first <= middle` and `middle < last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_less_than_transitive`

```click
theorem uint64_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}
```

Transitivity of unsigned 64-bit order: `first < middle` and `middle < last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_less_equal_transitive`

```click
theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}
```

Transitivity of unsigned 64-bit order: `first <= middle` and `middle <= last` give `first <= last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint64_less_equal_and_not_less_than_implies_equal`

```click
theorem uint64_less_equal_and_not_less_than_implies_equal(left: uint64, right: uint64) {
    requires left <= right;
    requires not left < right;

    ensures left == right;
}
```

An unsigned 64-bit value at most another and not below it is equal to it. A loop proof uses it for the element a step just reached: `k <= i` and `not k < i` give `k == i`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_less_than_less_equal_transitive`

```click
theorem int64_less_than_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}
```

Transitivity of signed 64-bit order: `first < middle` and `middle <= last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_less_equal_less_than_transitive`

```click
theorem int64_less_equal_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}
```

Transitivity of signed 64-bit order: `first <= middle` and `middle < last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_less_than_transitive`

```click
theorem int64_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}
```

Transitivity of signed 64-bit order: `first < middle` and `middle < last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `int64_less_equal_transitive`

```click
theorem int64_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}
```

Transitivity of signed 64-bit order: `first <= middle` and `middle <= last` give `first <= last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `uint32_greater_than_implies_reversed_less_than`

```click
theorem uint32_greater_than_implies_reversed_less_than(greater: uint32, lower: uint32) {
    requires greater > lower;

    ensures lower < greater;
}
```

**Meaning:** Given its listed requirements, proves `lower < greater`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_less_than_implies_reversed_greater_than`

```click
theorem uint32_less_than_implies_reversed_greater_than(lower: uint32, greater: uint32) {
    requires lower < greater;

    ensures greater > lower;
}
```

**Meaning:** Given its listed requirements, proves `greater > lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_greater_equal_implies_reversed_less_equal`

```click
theorem uint32_greater_equal_implies_reversed_less_equal(greater: uint32, lower: uint32) {
    requires greater >= lower;

    ensures lower <= greater;
}
```

**Meaning:** Given its listed requirements, proves `lower <= greater`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `uint32_less_equal_implies_reversed_greater_equal`

```click
theorem uint32_less_equal_implies_reversed_greater_equal(lower: uint32, greater: uint32) {
    requires lower <= greater;

    ensures greater >= lower;
}
```

**Meaning:** Given its listed requirements, proves `greater >= lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_nonnegative_predecessor_upper_bound`

```click
theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures value - 1 <= bound;
}
```

**Meaning:** Given its listed requirements, proves `value - 1 <= bound`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_equal_less_than_transitive`

```click
theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_equal_transitive`

```click
theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}
```

**Meaning:** Given its listed requirements, proves `first <= last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_than_transitive`

```click
theorem int32_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_than_less_equal_transitive`

```click
theorem int32_less_than_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_greater_equal_transitive`

```click
theorem int32_greater_equal_transitive(last: int32, middle: int32, first: int32) {
    requires last >= middle;
    requires middle >= first;

    ensures last >= first;
}
```

**Meaning:** Given its listed requirements, proves `last >= first`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_greater_equal_implies_reversed_less_equal`

```click
theorem int32_greater_equal_implies_reversed_less_equal(greater: int32, lower: int32) {
    requires greater >= lower;

    ensures lower <= greater;
}
```

**Meaning:** Given its listed requirements, proves `lower <= greater`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_equal_implies_reversed_greater_equal`

```click
theorem int32_less_equal_implies_reversed_greater_equal(lower: int32, greater: int32) {
    requires lower <= greater;

    ensures greater >= lower;
}
```

**Meaning:** Given its listed requirements, proves `greater >= lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_equal_and_not_less_than_implies_equal`

```click
theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right;
}
```

**Meaning:** Given its listed requirements, proves `left == right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_less_equal_and_not_equal_implies_less_than`

```click
theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right;
}
```

**Meaning:** Given its listed requirements, proves `left < right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_greater_equal_and_not_greater_than_implies_equal`

```click
theorem int32_greater_equal_and_not_greater_than_implies_equal(left: int32, right: int32) {
    requires left >= right;
    requires not (left > right);

    ensures left == right;
}
```

**Meaning:** Given its listed requirements, proves `left == right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## Array specifications

### `count`

```click
function count(p: int32[], lo: int32, hi: int32, x: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of elements equal to `x` in the half-open range `lo..hi` of the `int32` array reference `p`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `permutation`

```click
predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}
```

**Meaning:** States that `a` and `b` contain every `int32` value the same number of times in `lo..hi`. Unfolding exposes equality of two `count` calls under a universal quantifier.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(permutation)` when a proof needs the predicate body.

## Byte-range specifications

### `byte_count`

```click
function byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of bytes equal to `value` in the half-open range `lo..hi`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `bytes_equal`

```click
predicate bytes_equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    (0u64..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}
```

**Meaning:** States that the `len` bytes starting at `left_lo` and `right_lo` are pairwise equal. Offsets and lengths are `size_t` values.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_equal)` when a proof needs the predicate body.

### `bytes_equal_range`

```click
predicate bytes_equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}
```

**Meaning:** States that `left` and `right` are pairwise equal throughout the same half-open range `lo..hi`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_equal_range)` when a proof needs the predicate body.

### `bytes_all_equal`

```click
predicate bytes_all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that every byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_all_equal)` when a proof needs the predicate body.

### `bytes_contains`

```click
predicate bytes_contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that at least one byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_contains)` when a proof needs the predicate body.

### `bytes_all_not_equal`

```click
predicate bytes_all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}
```

**Meaning:** States that every byte in `lo..hi` differs from `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_all_not_equal)` when a proof needs the predicate body.

## C-string specifications

### `cstr_prefix`

```click
predicate cstr_prefix(bytes: uint8[], len: uint64) {
    forall (k: uint64) { k < len implies bytes[k] != '\0' }
}
```

**Meaning:** States that the first `len` bytes contain no null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_prefix)` when a proof needs the predicate body.

### `cstr_len`

```click
predicate cstr_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        cstr_prefix(bytes, len) and
        bytes[len] == '\0'
}
```

**Meaning:** States that `len` is a `size_t` length below `SIZE_MAX`, the
complete prefix through its terminator is readable, the preceding bytes contain
no null terminator, and byte `len` is a null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_len)` when a proof needs the predicate body.

### `cstr`

```click
predicate cstr(bytes: uint8[]) {
    exists (len: uint64) {
        cstr_len(bytes, len)
    }
}
```

**Meaning:** States that the byte array has some exact specification-level C-string length.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr)` when a proof needs the predicate body.

### `cstr_readable_len`

```click
predicate cstr_readable_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        forall (k: uint64) { k < len implies bytes[k] != '\0' } and
        bytes[len] == '\0' and
        forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
}
```

**Meaning:** States that `len` is a `size_t` C-string length below
`SIZE_MAX`, the complete prefix through its terminator is dynamically viewable,
the prefix has no embedded terminator, and every byte through the null
terminator is defined.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_readable_len)` when a proof needs the predicate body.

### `cstr_readable_len_unique`

```click
theorem cstr_readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) { k < left implies bytes[k] != '\0' };
    requires bytes[left] == '\0';
    requires forall (k: uint64) { k < right implies bytes[k] != '\0' };
    requires bytes[right] == '\0';

    ensures left == right by {
        have left < right or not (left < right) by {
            if left < right {
                assumption();
            } else {
                assumption();
            }
        }
        cases {
            left < right => {
                instantiate(forall (k: uint64) { k < right implies bytes[k] != '\0' }, left)
                    using { left < right; }
                contradiction(bytes[left] == '\0');
            }
            not (left < right) => {
                have right < left or not (right < left) by {
                    if right < left {
                        assumption();
                    } else {
                        assumption();
                    }
                }
                cases {
                    right < left => {
                        instantiate(forall (k: uint64) { k < left implies bytes[k] != '\0' }, right)
                            using { right < left; }
                        contradiction(bytes[right] == '\0');
                    }
                    not (right < left) => {
                        have left <= right by {
                            simp();
                        }
                        apply(uint64_less_equal_and_not_less_than_implies_equal(left, right)) using {
                            left <= right;
                            not (left < right);
                        }
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

### `cstr_readable`

```click
predicate cstr_readable(bytes: uint8[]) {
    exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
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

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_readable)` when a proof needs the predicate body.

### `cstr_bounded`

```click
predicate cstr_bounded(bytes: uint8[], max: uint64) {
    exists (k: uint64) { k < max and bytes[k] == '\0' }
}
```

**Meaning:** States that a null terminator occurs before the exclusive bound `max`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_bounded)` when a proof needs the predicate body.

### `cstr_len_is_viewable`

```click
theorem cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        unfold(cstr_len);
        simp();
    }
}
```

**Meaning:** Given an exact C-string length, exposes the viewability of the
prefix and its terminator as a separate fact for a subsequent proof step.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/cstr_viewable_witness.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_viewable_witness.md) checks this witness projection.

### `cstr_len_has_prefix`

```click
theorem cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        unfold(cstr_len);
        simp();
    }
}
```

**Meaning:** Given its listed requirements, proves `cstr_prefix(bytes, len)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `cstr_len_has_terminator`

```click
theorem cstr_len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures bytes[len] == '\0' by {
        unfold(cstr_len);
        simp();
    }
}
```

**Meaning:** Given its listed requirements, proves `bytes[len] == '\0'`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## External C contracts

These declarations cover the narrow byte-oriented libc slice supported by Click.
They are body-less assumptions: callers must satisfy their requirements, and
Click does not verify an implementation of the external function.

### `__click_constant_p_unknown`

```click
extern int32 __click_constant_p_unknown() {
    ensures result == 0 or result == 1;
}
```

**Meaning:** The value of the GNU builtin `__builtin_constant_p`, which the C
frontend lowers to a call of this function. Whether the compiler folds the
builtin's operand to a constant depends on optimization, so nothing is known
about the result beyond its being 0 or 1, and a proof covers both.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/c_builtin_constant_p.md`](https://github.com/clicklang/click/blob/master/mdtests/c_builtin_constant_p.md) checks that a claim must hold for both values.

### `memcpy`

```click
extern uint8* memcpy(uint8 destination[], const uint8 source[], uint64 bytes) {
    requires viewable(source[0..bytes]);
    owns destination[0..bytes];
    requires separate(memory(destination[0..bytes]), memory(source[0..bytes]));
    ensures result == destination;
    ensures bytes_equal(destination, 0u64, old(source), 0u64, bytes);
}
```

**Meaning:** Copies `bytes` bytes, a `size_t` count as in C, from a readable, non-overlapping source to
an owned destination and returns the destination pointer. This exact
standard-library declaration also carries the checked representation-copy
effect: after the call, each initialized typed cell whose complete byte
representation lies in the copied range is established at the mapped
destination offset. A source cell the copy would split, a symbolic range, an
unaligned destination, and an untyped source establish no typed value. The
effect is bound to this declaration, not to the name `memcpy`.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/byte_representation_scalar_copy.md`](https://github.com/clicklang/click/blob/master/mdtests/byte_representation_scalar_copy.md) checks its typed-copy effect.

### `memcmp`

```click
extern int32 memcmp(const uint8 left[], const uint8 right[], uint64 bytes) {
    requires viewable(left[0..bytes]);
    requires viewable(right[0..bytes]);
    requires forall (k: uint64) { k < bytes implies defined(left[k]) and defined(right[k]) };
    ensures result == 0 implies bytes_equal(left, 0u64, right, 0u64, bytes);
    ensures result != 0 implies not bytes_equal(left, 0u64, right, 0u64, bytes);
}
```

**Meaning:** Reads both `bytes`-long byte ranges (a `size_t` count, as in C) without mutation and distinguishes equal
from unequal prefixes by whether the result is zero.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](https://github.com/clicklang/click/blob/master/mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md) checks its range and definedness preconditions at a call.

### `memset`

```click
extern uint8* memset(uint8 destination[], int32 value, uint64 bytes) {
    requires 0 <= value;
    requires value <= 255;
    owns destination[0..bytes];
    ensures result == destination;
    ensures (0u64..bytes).all(|k| {
        defined(destination[k]) and destination[k] == value
    });
}
```

**Meaning:** Fills `bytes` bytes (a `size_t` count, as in C) of an owned
destination with a value Click can represent as `unsigned char`, and returns the
destination pointer. C converts any `int` fill value to `unsigned char`; Click
models that narrowing only for a representable value, so the contract requires
one.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/c_builtin_memset_header_checks_its_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/c_builtin_memset_header_checks_its_contract.md) refuses a call whose fill value is outside its precondition's range.

### `strlen`

```click
extern uint64 strlen(const uint8* bytes) {
    requires cstr_readable(bytes);
    ensures result < 18446744073709551615u64;
    ensures viewable(bytes[0..result + 1u64]);
    ensures forall (k: uint64) { k < result implies bytes[k] != '\0' };
    ensures bytes[result] == '\0';
    ensures cstr_readable_len(bytes, result);
    ensures old(bytes[0]) == '\0' implies result == 0u64;
}
```

**Meaning:** Returns the `size_t` length of a dynamically viewable,
null-terminated byte string without mutation, as C's `strlen` does. The result satisfies the readable-length relation and
points at its null terminator; `cstr_readable_len_unique` can connect it to an
independently framed witness. The separate `old(bytes[0])` consequence retains
the concrete empty-string guarantee.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](https://github.com/clicklang/click/blob/master/mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md) checks its empty-string length consequence.

## Namespace and extension rules

Standard-library definitions share the logic-declaration namespace with user
Click definitions. A user predicate, pure function, resource, or theorem can't
redefine a prelude name. A C function contract can have the same name as a
prelude pure function when no user Click definition creates a conflict.

To add a public symbol:

1. Add its declaration to `stdlib/prelude.click`.
2. Add a focused mdtest that uses it from an ordinary sidecar.
3. Add its semantic entry here; the inventory and exact-declaration checks fail
   until this page agrees with the source.
4. Add general prover or kernel support only when the definition exposes a
   reusable reasoning gap. Don't hard-code a domain-specific library name into
   the kernel merely because it is useful.

### `integer_to_int8_round_trip`

```click
theorem integer_to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z;
}
```

An Integer within the exact `int8` range retains its value after conversion
to that machine type and back. Both bounds are required.


### `integer_to_int16_round_trip`

```click
theorem integer_to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z;
}
```

An Integer within the exact `int16` range retains its value after conversion
to that machine type and back. Both bounds are required.

### `integer_to_int32_round_trip`

```click
theorem integer_to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z;
}
```

An Integer within the exact `int32` range retains its value after conversion
to that machine type and back. Both bounds are required.

### `integer_to_uint8_round_trip`

```click
theorem integer_to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z;
}
```

An Integer within the exact `uint8` range retains its value after conversion
to that machine type and back. Both bounds are required.

### `integer_to_uint16_round_trip`

```click
theorem integer_to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z;
}
```

An Integer within the exact `uint16` range retains its value after conversion
to that machine type and back. Both bounds are required.

### `integer_to_uint32_round_trip`

```click
theorem integer_to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z;
}
```

An Integer within the exact `uint32` range retains its value after conversion
to that machine type and back. Both bounds are required.

### `integer_to_int64_round_trip`

```click
theorem integer_to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z;
}
```

An Integer within the exact `int64` range retains its value after conversion
to that machine type and back. Both bounds are required.

### `integer_to_uint64_round_trip`

```click
theorem integer_to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z;
}
```

An Integer within the exact `uint64` range retains its value after conversion
to that machine type and back. Both bounds are required.

## Mathematical truncating division

These Integer laws use truncation toward zero, independently of native machine
widths and of the planned Euclidean `/` and `%` operators. They do not establish
native division or narrowing safety.

### `integer_truncation_identity`

```click
theorem integer_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}
```

### `integer_positive_divisor_remainder_lower`

```click
theorem integer_positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}
```

### `integer_positive_divisor_remainder_upper`

```click
theorem integer_positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}
```

### `integer_nonnegative_dividend_remainder`

```click
theorem integer_nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}
```

### `integer_nonpositive_dividend_remainder`

```click
theorem integer_nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}
```


### `integer_multiply_add`

```click
theorem integer_multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        arithmetic_certificate rules {
            integer_polynomial_identity bounds [] => (a + b) * c == a * c + b * c;
            conclusion 0;
        }
    }
}
```


### `integer_floor_from_remainder`

```click
theorem integer_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q + -1);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; 0 <= r; }
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { arithmetic() using { value == q + -1; } }
            rewrite(value + 1 == q);
            arithmetic() using { n == q * d + r; r < 0; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        }
    }
}
```


### `integer_ceiling_from_remainder`

```click
theorem integer_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q + 1);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; r <= 0; }
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { arithmetic() using { value == q + 1; } }
            rewrite(value + -1 == q);
            arithmetic() using { n == q * d + r; 0 < r; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        }
    }
}
```


### `integer_positive_divisor_quotient_lower`

```click
theorem integer_positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        arithmetic_certificate rules {
            premise 0: bound * d <= n => bound * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => bound <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}
```


### `integer_positive_divisor_quotient_upper`

```click
theorem integer_positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        arithmetic_certificate rules {
            premise 0: n <= bound * d => n <= bound * d;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => truncating_quotient(n, d) <= bound;
            conclusion 0;
        }
    }
}
```


### `integer_positive_divisor_quotient_strict_lower`

```click
theorem integer_positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { arithmetic() using { bound * d < n; } }
        apply(integer_positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { arithmetic() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            } }
            if n <= 0 {
                have 0 < d by { arithmetic() using { 1 <= d; } }
                apply(integer_nonpositive_dividend_remainder(n, d));
                apply(integer_truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (bound * d < n) by { arithmetic() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                } }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { arithmetic() using { not (n <= 0); } }
                have 0 * d <= n by { arithmetic() using { 0 <= n; } }
                apply(integer_positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { arithmetic() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                } }
                contradiction(bound < 0);
            }
        }
    }
}
```

### `integer_positive_divisor_quotient_strict_upper`

```click
theorem integer_positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { arithmetic() using { n < bound * d; } }
        apply(integer_positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { arithmetic() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            } }
            if 0 <= n {
                have 0 < d by { arithmetic() using { 1 <= d; } }
                apply(integer_nonnegative_dividend_remainder(n, d));
                apply(integer_truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (n < bound * d) by { arithmetic() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                } }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { arithmetic() using { not (0 <= n); } }
                have n <= 0 * d by { arithmetic() using { n <= 0; } }
                apply(integer_positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { arithmetic() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                } }
                contradiction(0 < bound);
            }
        }
    }
}
```

### `integer_lower_correction_bound`

```click
theorem integer_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            assumption();
        } else {
            have q == lower by { arithmetic() using { lower <= q; not (lower + 1 <= q); } }
            have n == lower * d + r by {
                rewrite(lower == q);
                assumption();
            }
            have not (r < 0) by { arithmetic() using { lower * d <= n; n == lower * d + r; } }
            contradiction(r < 0);
        }
    }
}
```


### `integer_upper_correction_bound`

```click
theorem integer_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            assumption();
        } else {
            have q == upper by { arithmetic() using { q <= upper; not (q <= upper + -1); } }
            have n == upper * d + r by {
                rewrite(upper == q);
                assumption();
            }
            have not (0 < r) by { arithmetic() using { n <= upper * d; n == upper * d + r; } }
            contradiction(0 < r);
        }
    }
}
```

### `integer_multiply_order_nonnegative`

```click
theorem integer_multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: 0 <= factor => 0 <= factor;
            integer_multiply_order bounds [0, 1] => a * factor <= b * factor;
            conclusion 0;
        }
    }
}
```

### `integer_multiply_order_nonpositive`

```click
theorem integer_multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: factor <= 0 => factor <= 0;
            integer_multiply_order bounds [0, 1] => b * factor <= a * factor;
            conclusion 0;
        }
    }
}
```

### `integer_scaled_product_bounds`

```click
theorem integer_scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer_multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: lower <= 0 => lower <= 0;
                integer_multiply_order bounds [0, 1] => lower * size <= lower * amount;
                conclusion 0;
            }
        }
        arithmetic() using { lower * size <= lower * amount; lower * amount <= value * amount; }
    }
    ensures value * amount <= upper * size by {
        apply(integer_multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: 0 <= upper => 0 <= upper;
                integer_multiply_order bounds [0, 1] => upper * amount <= upper * size;
                conclusion 0;
            }
        }
        arithmetic() using { value * amount <= upper * amount; upper * amount <= upper * size; }
    }
}
```

### `int32_remainder_to_integer`

```click
theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Connects a defined signed machine remainder to mathematical truncation. Native definedness excludes both a zero divisor and `INT32_MIN % -1`; a nonzero mathematical divisor alone does not establish that the C operation is defined.
