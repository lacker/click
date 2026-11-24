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
  is Rust's cast. Arithmetic search now expands to ordinary tactics and
  library laws; its former public certificate syntax has been removed.
- No certificate cache (closed 2026-10-15, launch review W4 and W5). The
  review proposed keeping `by auto` in sidecars and caching each claim's
  reconstructed certificate beside them, so verification would not search.
  Expansion already does this: `click expand` turns a slow smart site into
  the simple steps it found, which check without search, and the expansion
  is committed. A cache would be a second, hidden copy of the same proof.
- Expansion output stays as it is (closed 2026-10-17, launch review W4).
  `click expand` writes the ordinary steps selected by smart search,
  drops unused derivations, and shortens groups that `normalize();` proves.
  Marks name program points. Arithmetic derivations use `have` and library
  applications, with no separate numbered arithmetic-certificate language.
- A recorded non-void call has a source name, `R.result`, even when the
  program discards its result. The name selects the value retained at
  that call's exit. See the [call-result reference](../docs/reference/language/index.md#at)
  and the [discarded-result regression](../mdtests/a_discarded_call_result_keeps_its_call_name.md).
- `owns p` for a pointer is the pointer's own slot. `owns *p` is what it
  points at.
- A separate tactic for conjunction and disjunction goals was dropped;
  `close()` closes them.
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
  `load<uint8>(byte_offset(p, n))`.
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
  and memory in about thirty places. Diagnostics and `click expand` show
  the record (`record { first.v: ... }`; a comment in expansion output),
  as the maintainer decided on 2026-10-14 (launch review item M4).
- A call binds a callee's instance binder automatically when only one
  binding is possible, and never chooses between two.
- `diverges` stays on the signature and `decreases` stays a clause: one is a
  property of the function, the other a measure with an expression.
- Frames for owned cells stay explicit: a contract that owns a cell may
  change it unless an `ensures` says otherwise. Closed 2026-10-14 after
  three measured prototypes of a default frame (an owned cell unchanged
  unless an `ensures` or `produces` names it or a `writes` clause lists
  it), each proved by the callee like a written `ensures`. Over all owned
  cells about 215 gate mdtests and 9 example sidecars failed, mostly small
  tests that write an owned range; over struct fields only, about 84
  contracts needed `writes`; over fields held through a resource, about 40
  needed `writes` while 7 restated frames in the examples became
  removable. The default also hid itself from proofs whose claims each
  carry their own `by`. A frame is short to write and says what the
  caller may rely on; a default that writers must opt out of cost more
  than it saved. `owns X` replaced `consumes X; produces X;` and `owns *s`
  covers a whole struct; a cell a contract only views needs no frame.
- Program points stay named by source position (`region(N)`, `read(N)`,
  `loop(N)`). Closed 2026-10-14: neither source-named points nor a
  `click migrate` renumbering tool is planned; the implicit tail and `step()`
  avoid positions in most proofs.
- The repository root keeps `design/`, `roadmap/` and `bugs/` beside the
  product. Closed 2026-10-14: the maintainer judged the mix not a real
  problem.
- Read permission stays `views` (a call-scoped shared loan) and `owns`;
  fractional or counted read permissions are deferred until a program needs
  a reader-writer pattern (design review M3, split 2026-10-14). Closed
  2026-10-16: the library `memcpy` and `memcmp` contracts read under
  `views`, as every external load needs a covering viewed or owned
  resource. `viewable` stays a bounds fact with no read authority.

## Strengths the launch review credited

The 2026-10-12 launch design review, whose items are all closed, credited
these strengths. They are recorded so later fixes do not trade them away:
verification of unchanged source with pinned hashes; deterministic verdicts
from work budgets; smart search never trusted, expansion and audit
re-checked; documentation tied to passing fixtures; precise statements of
what is proved (termination, undefined behavior, `diverges`); readable
resource verbs with the write footprint equal to ownership; allocation
lifetime separate from access; candid scoping such as Adler-32's "remains
unproved".
