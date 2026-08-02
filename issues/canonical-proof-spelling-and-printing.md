# Canonicalize proof spelling and generated ranges

## Problem

The parser accepts several harmlessly equivalent spellings, while repository
examples and generated text often choose the noisier one. Two cases are common:

```click
have P by { simp(); }

loadable((owner->data)[0..owner->cap])
```

Click already supports the clearer one-line smart proof:

```click
have P by simp;
```

It also accepts an unparenthesized field-backed range:

```click
loadable(owner->data[0..owner->cap])
```

The contract-segment renderer currently adds parentheses whenever the range
base is a field expression, even though field access binds naturally as the
range base and the shorter form is used elsewhere in the documentation. This
noise compounds inside `old`, `memory`, `separate`, snapshots, and expanded
premise lists.

## Canonical style

- Prefer `have P by simp;` and the corresponding existing `by auto;` and
  `by frame;` spellings for one-operation smart proofs.
- Use `by { ... }` for multi-step scripts and for simple proof leaves that do
  not have a standalone proof-clause spelling.
- Render field-backed indexing and ranges without redundant parentheses:
  `owner->data[i]`, `owner->data[lo..hi]`, and
  `old(owner->data[lo..hi])`.
- Retain parentheses where precedence or a compound pointer expression
  actually requires them, such as `(p + offset)[0..n]`.

This is primarily a canonical-source and printer cleanup. It should not add a
general formatter, redesign proof clauses, or reject valid multi-step block
proofs.

## Scope

1. Remove the field-specific parenthesization from canonical contract-segment
   rendering, after confirming round-trip parsing for indexing, ranges,
   snapshots, `old`, and memory propositions.
2. Migrate repository occurrences of a single `simp()` block to `by simp;`
   where the two forms have the same current-frontier semantics.
3. Normalize nearby documentation examples to the same style.
4. Add focused parser/printer round-trip tests so future certificate changes do
   not reintroduce unnecessary parentheses.

Do not rewrite `have P by { normalize(); }` to `by simp;` merely to make it
shorter. `normalize()` is a simple context-free certificate leaf, while
`simp` is smart. Preserve the intended smart/simple choice.

## Dependencies

This issue can be implemented independently of the exact-premise cleanup. If
both are in flight, apply the exact-premise migration first to reduce conflicts
in certificate-heavy example files.

## Acceptance criteria

- Canonical rendering emits `owner->field[index]` and
  `owner->field[start..end]` without redundant parentheses.
- Parentheses remain around genuinely compound bases when required for the
  intended parse.
- Rendered ranges round-trip through the ordinary Surface Click parser in
  current, `old`, and `at` contexts.
- Repository examples use `have P by simp;` for single smart simplification
  proofs unless a block is intentionally demonstrating script syntax.
- No tactic semantics or smart/simple classifications change.
- Relevant documentation and snapshots are updated.
- The default test suite passes.
