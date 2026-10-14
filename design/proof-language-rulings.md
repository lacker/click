# Proof-language rulings

The 2026-10 design review of Click's surface language closed these
questions. Each is a decision with its reason, kept so it is not reopened
without one. Rust function contracts use Rust signatures and `impl` blocks;
the parser refuses C-shaped function contracts and `->` field access for Rust
sources. The hash-pinned migration fixtures stay unchanged and are adapted
only by the tests that read them.

- `unfold` keeps all of its meanings: one equation of a function call, a
  predicate made transparent for the rest of the branch, and one layer of a
  resource, which for an `authorized` member also accounts for the
  population. Each opens a definition one level; a word per target kind
  would add vocabulary without removing a choice.
- The other words with several uses stay (closed 2026-10-14). Each use sits
  in a position no other use can occupy: `count(r(args))` is the
  population operator only when its single argument is a resource call,
  and the prelude `count` takes four arguments; `fold` is a range method
  after `.` and a resource tactic in statement position; `function` starts
  a pure function at top level and is the `function` region selector in a
  proof; `as` names what a structural form binds, and in a Rust sidecar it
  is Rust's cast. Arithmetic-certificate step names are words only inside
  `arithmetic_certificate { ... }` and are listed apart from the general
  word index.
- `owns p` for a pointer is the pointer's own slot. `owns *p` is what it
  points at.
- A separate tactic for conjunction and disjunction goals was dropped;
  `assumption()` closes them.
- `requires`, `ensures`, `fact` and `invariant` stay four words: each says
  where its proposition holds.
- `requires` takes no label. Requirement labels were removed on 2026-09-23
  when proofs began citing a precondition by its proposition, and nothing
  would read one. A resource's `fact` takes none either: a refused fold
  names the fact by its declaration. `ensures` and `invariant` take a
  label, which names the claim in a failure.
- A range at another width gets no form. Closed 2026-10-08 after an
  inventory by text search: no Click source names a second width for a
  range. Reading at another width happens in C (`(unsigned char*)(void*) q`,
  `memcpy` on a wider object, about 48 files) and the kernel's byte view
  handles it (`docs/internals/byte-representation.md`). A specification that
  must state one byte of a wider cell writes the explicit load,
  `load_uint8(byte_offset(p, n))`.
- Holding a resource, viewed or owned, lets C read the memory it owns
  directly; a write needs `unfold`, and a child's memory is not read
  through. The views are attached to the owner and retire with it. The
  kernel derives them again wherever it makes the owner anew: at a loop
  head, from the definition or under the invariants, and at a fold of a
  resource with fields, as views of the cells the fold consumed.
- A C++ reference local reads in a proof as a reference parameter does:
  `r` is the referent and `&r` its address. A struct reference local waits
  on the importer admitting one.
- A resource without fields holds a child that has them by a hidden
  record, which remembers the child's values across a fold. A rule under
  which each unfold yields fresh values was considered and dropped: the
  kernel treats a fieldless resource's body as a function of its arguments
  and memory in about thirty places.
- A call binds a callee's instance binder automatically when only one
  binding is possible, and never chooses between two.
- `diverges` stays on the signature and `decreases` stays a clause: one is a
  property of the function, the other a measure with an expression.
