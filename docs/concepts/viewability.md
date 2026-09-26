# Viewable ranges

A logical memory read such as `p[k]` denotes a value even when the proof has
no viewable range for it. The term is total: it can appear in an equality, a
function argument, or under a quantifier without silently adding a validity
condition. In particular, `p[k] == p[k]` is true without granting any right to
read `p[k]` in C.

Use `defined(p[k])` to claim that the typed read is valid at that snapshot.
This checks bounds, lifetime, and initialization. A value equality does not
prove validity: even `p[k] == 7` cannot initialize fresh heap memory. An
explicit validity claim under an existential belongs to that same witness.
`at(mark, defined(p[k]))` concerns the marked snapshot and does not by itself
establish validity after a free or a memory change.

C execution still checks every actual read, including call arguments. For
external memory it also needs a resource permitting the access; neither a
logical value nor a pure validity claim grants that permission. Resource
expressions that read memory to identify their footprint use checked reads.
See [Resources and memory permissions](resources.md).

This separation applies to memory reads. Existing conditions for partial C
arithmetic, such as signed overflow and division by zero, remain in force.
For an array parameter:

<!-- verified-example: mdtests/pointer_range.md -->
```c
int32 first(int32 p[]) {
    return p[0];
}
```

the contract needs:

<!-- verified-example: mdtests/pointer_range.md -->
```click
int32 first(int32 p[]) {
    views p[0..1];
    ensures result == p[0] by auto;
}
```

Viewed and owned memory resources imply viewability for the range they cover. Use
`viewable(...)` when you need memory-viewability information without granting
access permission, or when the proof needs a larger range than any single
access resource provides.

`viewable(segment)` is the proposition form of the same memory-viewability fact.
It is useful inside predicate-like positions, especially composite resource
`fact` clauses:

<!-- verified-example: mdtests/pointer_range.md -->
```click
fact viewable(data[0..cap]);
```

## Ranges

`viewable` uses half-open ranges:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires viewable(p[0..n]);
```

This covers indices `0` through `n - 1`. For `int32 p[]`, each element is a
four-byte access. For `uint8 p[]`, each element is a one-byte access.

## What a range fact means

`viewable(p[a..b])` says two things together:

- `a..b` is a valid 32-bit byte extent: `a <= b`, and the element count `b - a`
  is small enough that scaling it by the element width does not wrap. For
  `int32` elements that count has to sit in `0..=1073741823`.
- those bytes are viewable.

Both halves are the fact, so both travel with it. Wherever a range is *stated* —
a `requires`, an `owns`/`views` clause, a composite resource's contained range,
a loop invariant, a theorem premise — the extent half is available as a fact
beside the viewability half, and a proof does not restate it. Wherever the range
has to be *established* — a C call site, applying a theorem whose premise is a
range, a loop invariant's entry and back edge — the extent half is owed along
with the viewability half.

A loop invariant is both at once, like any other invariant content: the head,
the body and the exit assume both halves, and the entry and every back edge owe
both. An invariant whose range is already known not to be an extent where it is
owed is refused there, as a false invariant, rather than read as owing nothing.

`separate(memory(p[a..b]), memory(q[c..d]))` includes the same validity
conditions for both ranges. A separation premise supplies the bounds; a
separation goal or call requirement must prove them. Observing or unfolding a
composite resource exposes the bounds of its contained memory ranges, so a
proof can use those bounds without repeating them in the resource definition.
Separation alone does not grant permission to read either range.

Stating a range whose extent is decidably invalid is refused where the clause is
prepared, so the two directions cannot be played against each other. At the
program's outer boundary, where no caller is verified, a contract's range is an
assumption about the environment in the same way the pointer being live is one:
writing `views p[0..n]` asserts that `n` really is a count of elements `p`
holds. Inside the program every use of that range is checked against the clause
that stated it.

The second half alone would be a weaker fact than it looks. An extent is
`(b - a) * width` in 32-bit arithmetic, so a count of `1 << 30` four-byte
elements scales to `0`: the range would be empty, vacuously viewable for any
pointer, and still spell "the elements `0..1 << 30`". Every rule that reads a
range at element granularity — placing a cell inside it, narrowing it,
concatenating two of them — therefore asks for the extent half first, whatever
the fact's origin. A range a proof established rather than stated carries no
such promise, and reading it as an element count is refused:

```text
`viewable(v[0..n])` is a premise here and was consulted, but it is not a valid
32-bit byte extent in this scope: `n <= 1073741823` is not an established fact
```

Since Click's surface has no unsigned comparison, the condition is stated in the
signed spelling above, as `0 <= b - a` together with `b - a <= 1073741823`.


A narrower viewability claim can also be covered by a wider one. The
displacement from the wider base plus the narrower claim's byte count must fit
inside the wider byte extent as an exact count. A 32-bit sum that wraps to a
small residue does not establish coverage. For symbolic byte sums, Click
requires bounds that keep the arithmetic nonnegative and unwrapped. The
kernel checks the addends and proves the computed end is no smaller than the
displacement before comparing that end with the covering span; a
constant-size element read can instead use the range's guarded element count.

## In a pure theorem

A theorem has no resource context: nothing is lent to it, nothing is consumed,
and applying it separates nothing. Readability is the one thing a range still
means without an owner, so a theorem states a range with `views`, and there it
is a hypothesis and nothing else:

<!-- verified-example: mdtests/theorem_views_states_a_readable_range.md -->
```click
theorem cell_of_a_viewed_range(v: int32[], lo: int32, hi: int32, k: int32) {
    views v[lo..hi];
    requires lo <= k;
    requires k < hi;
    ensures to_integer(v[k]) == to_integer(v[k]) by { simp(); }
}
```

The clause lowers to the proposition `viewable(v[lo..hi])` states, appended to
the theorem's requirements in the position it was written, and it carries the
extent half like any other stated range: the theorem's own proof assumes both
halves, and an application owes both. `requires viewable(v[lo..hi]);` in a
theorem means exactly the same thing.

`owns`, `consumes` and `produces` remain refused in a theorem, because a
theorem has nothing to take and nothing to hand back.

A `using` list holds propositions, so a `views` premise is named there by its
fact form:

<!-- verified-example: mdtests/c_proof_applies_a_views_theorem.md -->
```click
apply(element_of_a_viewed_range(a, 0, 3, 1)) using {
    viewable(a[0..3]);
}
```

Listing the range cites both of its halves. The application owes the extent
half beside the range, and each of its conditions joins the evidence wherever
it is an available fact, as it is beside a stated range, so the list does not
restate `0 <= n - lo` and `n - lo <= 1073741823`. An induction hypothesis's
range premise is cited the same way
(`mdtests/induction_hypothesis_cites_a_listed_range_with_its_extent.md`). A
range the proof narrowed to carries no such facts, so its halves are refused
until the proof establishes them
(`mdtests/induction_hypothesis_owes_the_range_extent.md`).

That is also the form the refusal prints when an application cannot establish
the premise, so what the reader is told to supply is what they write down. A C
proof supplies it from the readability its own `views` or `owns` clause gives
over that range, and a theorem applying another theorem — or its own induction
hypothesis — supplies it from its own `views` hypothesis, narrowed by the rule
in [Narrowing a range](#narrowing-a-range).

You can also write shifted ranges:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires viewable((p + 1)[0..n - 1]);
```

## Index bounds

A viewable range is not enough by itself if the index is symbolic. Click also needs
to know the index is inside the range:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires 0 <= k;
requires k < n;
requires viewable(p[0..n]);
views p[0..n];
ensures result == p[k] by auto;
```

Loops usually need invariants to preserve these bounds at every iteration.

## Narrowing a range

A viewability fact is also provable, not only findable. When the verifier cannot
see a range on its own, state it first and the step that needs it goes through:

<!-- verified-example: mdtests/have_viewable_prefix_of_a_range.md -->
```click
have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
```

<!-- verified-example: mdtests/have_viewable_single_cell.md -->
```click
have viewable(p[hi - 1..hi - 1 + 1]) by { simp(); }
```

Narrowing reads both ranges at element granularity. From `viewable(p[a..b])` it
concludes `viewable(p[c..d])` when order facts establish `a <= c`, `c <= d` and
`d <= b`: the elements `c..d` are then a contiguous part of the elements `a..b`.
All three are required. `c <= d` in particular is not assumed, so a reversed
range is refused rather than read as a negative extent, and a range reaching
past `b` is refused with the order fact it was missing:

```text
`transport using` cannot narrow `viewable(v[lo..hi])` to `viewable(v[lo..k])`:
narrowing a viewable range needs `k <= hi`, which is not an available fact
```

Narrowing also needs the range it starts from to be a valid byte extent — the
first half of [what a range fact means](#what-a-range-fact-means) — and this is
a real precondition rather than bookkeeping. A stated range carries it, so a
theorem whose premise is `viewable(v[lo..hi])` narrows it without writing the
bound down. A range the proof established itself does not, and narrowing it is
refused.

Narrowing itself is one decision, not two. It is part of the same viewability
rule set the verifier applies while lowering `p[hi - 1]` on its own, so a fact
of this kind can be written down and proved as well as found — in a pure theorem
as well as in a C proof. A C proof writes it the same way, over the range its
contract stated:

<!-- verified-example: mdtests/have_viewable_prefix_of_a_range_in_a_c_proof.md -->
```click
have viewable(a[0..k]) by { simp(); }
```

That matters for induction over an array range, where
the hypothesis needs the narrowed range as an exactly available fact before it
can be applied; see
[`fold_reading_a_viewed_array_is_nonnegative_over_its_own_range.md`](https://github.com/lacker/click/blob/master/mdtests/fold_reading_a_viewed_array_is_nonnegative_over_its_own_range.md).

## Old memory

`old(...)` reads from the function-entry state:

<!-- verified-example: mdtests/pointer_range.md -->
```click
ensures p[0] == old(p[0]) by auto;
```

This is how postconditions talk about preservation or change. The expression
inside `old(...)` still needs to be meaningful in the entry state, so memory
viewability and permission requirements still matter.

## Field resources

For struct fields, prefer field resources:

<!-- verified-example: mdtests/pointer_range.md -->
```click
views obj->ref_count;
consumes &obj->data;
```

Those resources imply viewability for the covered fields. A resource addressed
*through* a field reads that field to name itself, so the contract needs the link
cell too: `views node->left->augmented` is only meaningful next to a resource
covering `node->left`, such as `views &node->left` or a composite holding it, and
a `requires node->left != 0` guarding the link. A contract that names a segment
through a cell it does not hold is refused where it is prepared.

Explicit ranges remain useful when a proof needs a broader footprint than one
field:

<!-- verified-example: mdtests/pointer_range.md -->
```click
consumes obj[0..3];
```
