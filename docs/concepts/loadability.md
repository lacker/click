# Memory loadability

Pointer proofs start with loadability. Before Click can prove what a memory access
returns, it must know that the access is in bounds. For external memory, Click
also needs permission to access the range; see
[Resources and memory permissions](resources.md).

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

Viewed and owned memory resources imply loadability for the range they cover. Use
`loadable(...)` when you need memory-loadability information without granting
access permission, or when the proof needs a larger range than any single
access resource provides.

`loadable(segment)` is the proposition form of the same memory-loadability fact.
It is useful inside predicate-like positions, especially composite resource
`fact` clauses:

<!-- verified-example: mdtests/pointer_range.md -->
```click
fact loadable(data[0..cap]);
```

## Ranges

`loadable` uses half-open ranges:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires loadable(p[0..n]);
```

This covers indices `0` through `n - 1`. For `int32 p[]`, each element is a
four-byte access. For `uint8 p[]`, each element is a one-byte access.

## What a range fact means

`loadable(p[a..b])` says two things together:

- `a..b` is a valid 32-bit byte extent: `a <= b`, and the element count `b - a`
  is small enough that scaling it by the element width does not wrap. For
  `int32` elements that count has to sit in `0..=1073741823`.
- those bytes are loadable.

Both halves are the fact, so both travel with it. Wherever a range is *stated* —
a `requires`, an `owns`/`views` clause, a composite resource's contained range,
a loop invariant, a theorem premise — the extent half is available as a fact
beside the loadability half, and a proof does not restate it. Wherever the range
has to be *established* — a C call site, applying a theorem whose premise is a
range, a loop invariant's entry and back edge — the extent half is owed along
with the loadability half.

The second half alone would be a weaker fact than it looks. An extent is
`(b - a) * width` in 32-bit arithmetic, so a count of `1 << 30` four-byte
elements scales to `0`: the range would be empty, vacuously loadable for any
pointer, and still spell "the elements `0..1 << 30`". Every rule that reads a
range at element granularity — placing a cell inside it, narrowing it,
concatenating two of them — therefore asks for the extent half first, whatever
the fact's origin. A range a proof established rather than stated carries no
such promise, and reading it as an element count is refused:

```text
`loadable(v[0..n])` is a premise here and was consulted, but it is not a valid
32-bit byte extent in this scope: `n <= 1073741823` is not an established fact
```

Since Click's surface has no unsigned comparison, the condition is stated in the
signed spelling above, as `0 <= b - a` together with `b - a <= 1073741823`.

You can also write shifted ranges:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires loadable((p + 1)[0..n - 1]);
```

## Index bounds

A loadable range is not enough by itself if the index is symbolic. Click also needs
to know the index is inside the range:

<!-- verified-example: mdtests/pointer_range.md -->
```click
requires 0 <= k;
requires k < n;
requires loadable(p[0..n]);
views p[0..n];
ensures result == p[k] by auto;
```

Loops usually need invariants to preserve these bounds at every iteration.

## Narrowing a range

A loadability fact is also provable, not only findable. When the verifier cannot
see a range on its own, state it first and the step that needs it goes through:

<!-- verified-example: mdtests/have_loadable_prefix_of_a_range.md -->
```click
have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
```

<!-- verified-example: mdtests/have_loadable_single_cell.md -->
```click
have loadable(p[hi - 1..hi - 1 + 1]) by { simp(); }
```

Narrowing reads both ranges at element granularity. From `loadable(p[a..b])` it
concludes `loadable(p[c..d])` when order facts establish `a <= c`, `c <= d` and
`d <= b`: the elements `c..d` are then a contiguous part of the elements `a..b`.
All three are required. `c <= d` in particular is not assumed, so a reversed
range is refused rather than read as a negative extent, and a range reaching
past `b` is refused with the order fact it was missing:

```text
`transport using` cannot narrow `loadable(v[lo..hi])` to `loadable(v[lo..k])`:
narrowing a loadable range needs `k <= hi`, which is not an available fact
```

Narrowing also needs the range it starts from to be a valid byte extent — the
first half of [what a range fact means](#what-a-range-fact-means) — and this is
a real precondition rather than bookkeeping. A stated range carries it, so a
theorem whose premise is `loadable(v[lo..hi])` narrows it without writing the
bound down. A range the proof established itself does not, and narrowing it is
refused.

Narrowing itself is one decision, not two. It is part of the same loadability
rule set the verifier applies while lowering `p[hi - 1]` on its own, so a fact
of this kind can be written down and proved as well as found — in a pure theorem
as well as in a C proof. That matters for induction over an array range, where
the hypothesis needs the narrowed range as an exactly available fact before it
can be applied; see
[`fold_reading_an_array_is_nonnegative_over_its_own_range.md`](https://github.com/lacker/click/blob/master/mdtests/fold_reading_an_array_is_nonnegative_over_its_own_range.md).

## Old memory

`old(...)` reads from the function-entry state:

<!-- verified-example: mdtests/pointer_range.md -->
```click
ensures p[0] == old(p[0]) by auto;
```

This is how postconditions talk about preservation or change. The expression
inside `old(...)` still needs to be meaningful in the entry state, so memory
loadability and permission requirements still matter.

## Field resources

For struct fields, prefer field resources:

<!-- verified-example: mdtests/pointer_range.md -->
```click
views obj->ref_count;
consumes obj->data;
```

Those resources imply loadability for the covered fields. A resource addressed
*through* a field reads that field to name itself, so the contract needs the link
cell too: `views node->left->augmented` is only meaningful next to a resource
covering `node->left`, such as `views node->left` or a composite holding it, and
a `requires node->left != 0` guarding the link. A contract that names a segment
through a cell it does not hold is refused where it is prepared.

Explicit ranges remain useful when a proof needs a broader footprint than one
field:

<!-- verified-example: mdtests/pointer_range.md -->
```click
consumes obj[0..3];
```
