# Rust iterators: one generic model, per-type library contracts

Status: steps 1 and 2 done, step 3 under way and being revised: the
iterator is imported through its Rust interface (`next(&mut it)` returning
an `Option`), not as importer-made operations; see "Importing an iterator
through its Rust interface". Slice iterators under `"iterators": "library"`
are imported this way (`design/charon-trial/slice-iter`,
`examples/rust-iterators`, `examples/rust-iter-references`), and so are
`chunks_exact` iterators: `next` returns `Option<&[u8]>`, the slice a
library `Slice<u8>`, and `remainder()` is Rust's own call
(`examples/rust-chunks-exact` and the `chunks_exact` fixtures under
`design/charon-trial`). The remaining fixtures move next. A Rust unit with
`"iterators": "library"` imports its slice iterators as values of the
library's `SliceIter` (`library/rust/slice_iter.click`,
`design/charon-trial/slice-iter`); the switch is temporary and goes when
every slice-iterator fixture and adler2 have moved. `library/rust/chunks_exact.click`
declares `ChunksExact<T>` with `len`, `nth`, `remainder` and `after_next` and
the axioms relating them, and a proof reads a value with those methods. Every
Rust unit imports its `chunks_exact` iterators as values of that type, and
construction, `remainder()` and loops, including one that reads through each
chunk, are proved from the contract (`examples/rust-chunks-exact/chunks.click`,
every `chunks_exact` fixture, and adler2). The chunk iterators' hidden-state
model and the temporary `"iterators": "library"` unit option are removed. The
loop fact is a library function, `after(it, k)`, the iterator after `k` calls
of `next()`: a loop carries `iter == start.after(iterations)`. The loop's
starting iterator is spelled with the
existing state form, `at(loop(i).entry, iter)` (open question 2).

## Problem

Click currently models each supported Rust iterator kind by hand. Each kind
costs work in two places.

- **Importer lowering.** `src/languages/rust/lowering/` has `shared_arrays.rs`
  for `slice::Iter`, `enumerate.rs`, `ranges.rs` for `a..b` and `a..=b`, and
  `chunks.rs` for `ChunksExact`, about 830 lines in all. Each file turns one
  iterator type into hidden C locals and hand-written `next` code: a slice
  iterator's `_base`, `_length` and `_remaining`, or a chunk iterator's
  `_cursor`, `_remaining`, `_size` and `_tail`.
- **Accessor views.** `surface.rs` (`rust_iterator_method`,
  `rust_iterator_accessors`) maps each kind's Rust methods onto those hidden
  locals. For example, `iter.len()` on a slice iterator reads `_remaining`,
  and `iter.as_slice()` reads `_base + (_length - _remaining)`.

Proofs that go past the accessors have to reason about the hidden locals.
The adler2 proofs mention them about 2,700 times
(`__rust_mir_62_remaining` and others). Adding an iterator type means
another lowering file, another accessor table and another set of hidden
names. That cannot scale to the hundreds of stdlib types (and other
libraries' types) Click will eventually need.

## Principle

Iterators are a core part of Rust, so Click supports iterators **generically**.
Click does not special-case any particular iterator **type**. A type such as
`ChunksExact`, `slice::Iter`, `Enumerate` or `Range` is described by
contracts in the Click library, the same way `library/rust/vec.click`
describes `Vec<T>`. Those contracts are trusted: they are knowns, like
an `extern fn` contract. A later effort could verify the real implementations
against them. That is not part of this proposal.

## Generic iterator model (in Click)

- **An iterator value stands for the finite sequence of items it will still
  yield.** Click knows two things about any iterator value `it`:
  - `it.len()`: how many items are left. This is Rust's
    `ExactSizeIterator::len` where Rust has it.
  - `it.nth(k)`: the item the `k`-th following `next()` would return, for
    `k < it.len()`. It is a pure observation, not Rust's consuming
    `Iterator::nth`.
- **One law covers every `next()`.** When `it.len() > 0`, `next()` returns
  `Some(it.nth(0))`. Afterwards the iterator has `len() == old.len() - 1`
  and `nth(k) == old.nth(k + 1)`. When `it.len() == 0`, `next()` returns
  `None` and leaves the iterator unchanged.
- **The loop fact.** A `for x in it` loop provides `iterations` already. Let
  `start` be the iterator's value at loop entry. On pass `k`, where `k` is
  `iterations`:
  - the loop variable `x` is `start.nth(k)`;
  - `iter.len() == start.len() - k`.

  These facts follow from the `next` law by induction. No iterator type
  appears in them.

  As built, the loop fact is not a verifier rule. Each type's library file
  declares `after(it, k)`, `it` after `k` calls of `next()`, with the
  axioms `after(it, 0) == it`, `after_next(after(it, k)) == after(it, k +
  1)`, `len(after(it, k)) == len(it) - k` and `nth(after(it, k), j) ==
  nth(it, k + j)`. A loop states `iter == start.after(iterations)` as an
  ordinary invariant; the second axiom preserves it across a pass and the
  last gives the loop variable. The cost is one function and four axioms a
  type; the gain is that nothing in Click knows about iterator loops.

Nothing in this model knows what any particular iterator yields. That is
what the library contracts are for.

## Per-type contracts (in the library)

Each iterator type gets a short library file. It states only what the
constructor produces and the type's own extra methods. For example:

- `bytes.chunks_exact(n)`:
  - requires `n != 0`;
  - `len() == bytes.len() / n`;
  - `nth(k)` is the slice of length `n` starting at `bytes + k * n`;
  - `remainder()` is the last `bytes.len() % n` bytes. It is fixed: `next`
    leaves it unchanged.
- `bytes.iter()`: `len() == bytes.len()`, and `nth(k)` is `&bytes[k]`.
  `as_slice()` is the `len()` bytes ending at `bytes + bytes.len()`.
- `it.enumerate()`: `len()` is the inner iterator's `len()`, and `nth(k)` is
  `(k, inner.nth(k))`.
- `a..b`: `len()` is `b - a` when `a <= b` and zero otherwise, and `nth(k)` is
  `a + k`. `start` and `end` are the fields. `a..=b` is similar, with
  `start()`, `end()` and `is_empty()`.

Each of these is a set of `axiom`s or `extern fn` contracts over the
generic functions. None of them needs verifier code.

## What a proof looks like

`examples/rust-chunks-exact`:

```rust
let chunks = bytes.chunks_exact(4);
let tail = chunks.remainder();
for chunk in chunks { let first = chunk[0]; let last = chunk[3]; }
tail.len()
```

The proof combines the loop fact with the `chunks_exact` contract. On pass
`k`, `chunk` is `start.nth(k)`, which is `bytes + 4 * k` with length 4.
`iter.len() == bytes.len() / 4 - k` holds as well. The read bound
`4 * k + 4 <= bytes.len()` follows from `iter.len() > 0`, plus the
`integer::` quotient lemmas, cited explicitly. There is no cursor, no
remaining-byte count and no hidden name. The loop needs no invariant about
the iterator, only `decreases iter.len()`.

## Importing an iterator through its Rust interface

The importer imports an iterator the way it imports a `Vec`: through Rust's
own interface, with each Rust call a call whose contract is stated over the
library type. It does not take an iterator apart into C locals or invent
operations Rust does not have.

- **Construction** is the Rust call that builds the iterator, with Rust's
  signature: `<[T]>::iter(s: &[T]) -> Iter<T>`, `<[T]>::chunks_exact(s, n)`,
  and the `IntoIterator::into_iter` a `for` loop calls. Its contract says
  which library value it returns: `ensures result == slice_iter::iter(s);`.
- **`next`** is one call, `Iterator::next(it: &mut I) -> Option<Item>`. Its
  contract is the next law at that type, over `old(*it)` and `*it`, as
  `Vec::push`'s contract is over `old(*v)` and `*v`:

  ```text
  extern fn next(it: &mut Iter<u8>) -> Option<&u8> {
      owns *it;
      ensures len(old(*it)) == 0 implies result == None and *it == old(*it);
      ensures 0 < len(old(*it)) implies
          result == Some(as_ptr(as_slice(old(*it)))) and *it == after_next(old(*it));
      // facts that need the element size, at this type:
      ensures 0 < len(old(*it)) implies
          as_ptr(as_slice(*it)) == as_ptr(as_slice(old(*it))) + 1u64;
      ...
  }
  ```

- **A `for` loop** is what the compiler produced: a loop that calls
  `next(&mut it)` and matches the `Option`, `None` leaving the loop and
  `Some(x)` binding the item. The importer keeps the call and the `match`.
  The `Option` is a value of the library's `spec enum Option<T>` at the item
  type, `Option<&u8>` here, as `Option<u32>` already is.

The item a pass yields is then the `Some` payload. A `match` on a call
result whose contract says it is `Some(t)` binds the payload to `t` itself,
not to a fresh value equal to it (checked with `Option<u32>`: the payload of
`wrap(x)`, whose contract is `result == Some(x)`, is `x`). So the item is
`as_ptr(as_slice(start.after(k)))`, a term the loop's invariant already
names, and a read through it needs no name for a compiler temporary.

The per-kind lowering files, the `_left`, tag and pointer locals, and the
importer-made operations (`SliceIter::len`, `SliceIter::as_ptr`,
`SliceIter::after_next`, and the six `ChunksExact` ones) are removed. So are
`RustIteratorKind`, the per-kind accessor table and the old spellings
(`iter_remaining`, `<prefix>_cursor`, `__rust_mir_*_remaining`). A loop's
`iter` stays the local `next` borrows.

### What this needs

- **`Option` of a reference.** The importer types `Option<T>` only for a
  scalar, a crate enum or a type parameter
  (`library_argument_spelling`). `Option<&T>` (slice iterators) and
  `Option<&[T]>` (`chunks_exact`) need a pointer and a slice payload. Click
  itself already has such values: `Option<uint8*>::Some(p)` type-checks and
  verifies in a theorem.
- **`&mut` of a local library value.** Already supported:
  `design/charon-trial/vec-values` does `let mut v = Vec::new(); v.push(x)`.
- **The loop's `Option` split.** `match` on the `next` result splits on its
  tag. Knowing it is `Some` gives `0 < len(old(*it))` from the first
  `ensures` by the existing rule for an implication whose consequent the
  facts make an equation of two constructors (`docs/reference/rust.md`,
  Result values), and then the second `ensures` gives the payload.

## Open questions

1. **Pointer- and slice-valued items.** An iterator's items can be
   references or slices inside an `Option`. The first answer, keeping the
   `Option` as the importer's own tag, pointer and length locals, read
   through importer-made calls, made the item a compiler temporary that a
   proof could only name by a region number. Revised: the `Option` is a
   library value at the item type (see "Importing an iterator through its
   Rust interface").
2. **Naming `start`.** The loop fact needs the iterator's value at loop
   entry. Candidates:
   - `loop(i).start`, a new built-in like `iterations`;
   - the program's own local that the loop consumes, such as `chunks` in
     `for chunk in chunks`, read at loop entry;
   - an existing state form.
3. **Iterators advanced before the loop or resumed after a `break`.** In
   those cases `iterations` is not the number of items consumed. The loop
   fact is stated relative to the value at loop entry, so it still holds.
   A proof that relates it to construction must account for the earlier
   `next` calls.
4. **Quantified contracts.** `nth(k)` facts are `forall k`. Proofs
   instantiate them at `k = iterations`, explicitly for now. A future
   `solve` search for a single applicable library theorem (pending Vec work,
   task "Vec 2") would remove those citations. Simple checking must stay
   linear in the proof, so contracts must not be instantiated eagerly.
5. **Relation to a future "library interface" or "module interface".**
   Each per-type file is an interface: types, functions and contracts that
   are trusted now and verifiable later. If Click grows such a concept, these
   files should become its first instances.

## Migration

1. Done: the generic model plus the `ChunksExact` contract on
   `examples/rust-chunks-exact`, which settled open questions 1 and 2.
2. Done: the other `chunks_exact` fixtures, then adler2. The chunk
   iterators' hidden-state lowering and the `"iterators": "library"` unit
   option that let fixtures move one at a time are removed.
3. Slice iterators, `enumerate` and ranges onto their library contracts.
   Slice iterators: the model and one fixture
   (`design/charon-trial/slice-iter`) are in, behind the temporary unit
   option `"iterators": "library"`; the other fixtures and the adler2 tail
   loops follow, then the option and `shared_arrays.rs` go. A slice
   iterator's model is its remaining slice, `as_slice(it)`: there is no
   `nth` or `after`, and what `next()` leaves is stated by the importer's
   contract for the call at its element type, since a generic axiom cannot
   offset a `T*`.
   This includes inclusive ranges, currently blocked by
   `bugs/solve-exhausts-its-budget-spelling-premises-of-an-inclusive-range-loop.md`,
   which should be re-checked under the new model.
4. Remove the remaining per-kind lowering, the accessor table and the old
   spellings.
