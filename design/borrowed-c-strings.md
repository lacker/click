# Borrowed C strings: contract length binders and call-site assembly

Status: approved 2026-10-15, with an owning `cstr_at` body. The owning body,
the contract's choice of `views`, `owns`, or `consumes`/`produces`, and
call-site assembly from owned bytes are implemented. The binder form (c) and
the resource-term call map were implemented on per-call contract value
parameters (see [Kernel mechanism for (c)](#kernel-mechanism-for-c)), a
kernel concept the original proposal assumed already existed. The binder
surface was later replaced: a contract declares the length as a value
parameter, `let n: uint64; views cstr_at(bytes, n);`, the form named
contracts use, and a call map gives the value, `{ n: k }`; `_` is only the
count pattern's wildcard. The kernel mechanism below is unchanged. The
sections that follow keep the original binder spelling as the record of the
proposal. Assembly from viewed bytes is deferred (see
[(d)](#d-call-site-assembly-of-a-viewed-composite)). M3 landed: `memcpy` and
`memcmp` read under `views`.

`click::c::string` declares the C string:

```click
resource cstr_at(p: const uint8*, len: uint64) {
    owns p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and k < len + 1u64 implies defined(p[k]) };
}
```

The body owns the bytes, and a contract chooses how it holds them:

- `views cstr_at(p, n)` borrows the string read-only. An opened view exposes
  the bytes as views, so the callee cannot write them
  (`mdtests/cstr_at_viewed_string_cannot_be_written.md`).
- `owns cstr_at(p, n)` holds it exclusively and returns the same instance.
  The callee may write bytes inside the string and refold the same length
  (`mdtests/cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md`).
- `consumes cstr_at(p, n)` with `produces` changes it.

The length is a parameter of the instance, so it is fixed by the bytes
through the first terminator. Shortening a string is an unfold, a store of an
earlier terminator, and a fold of a smaller instance; the bytes after the new
terminator leave the instance as plain owned memory. Growing one requires
owning further bytes. An `owns` clause returns the instance it received, so a
function that changes the length must consume the old instance and produce
the new one: the `owns` form is refused
(`mdtests/cstr_at_owns_clause_cannot_shorten_the_string.md`) and the
consumes/produces form verifies
(`mdtests/cstr_at_consumes_and_produces_a_shorter_string.md`).

The goal is `strlen` and `label_copy` contracts that hold the string under
`views`, so the trusted `memcpy`/`memcmp` can read under `views` (M3) without
narrowing a claim. Two pieces were missing: a contract cannot name a length
its C signature does not carry (c), and a caller that holds only the bytes
cannot pass a `cstr_at` it never folded (d). Both are implemented, (d) for
owned bytes.

## (c) The length is an instance binder's argument

### What exists

Contracts already have binders for resource instances. `owns cell: R(args);`
declares a contract proof parameter (`ContractDefinition::proof_parameters`).
A call binds it from an explicit map, `step(f(x), { cell: c })`, or
automatically when exactly one binding is possible, and never chooses between
two (proof-language rulings). `cell.field` reads a field of the bound
instance and `old(cell.field)` its entry value. Resource arguments already
admit `_` in authority patterns. Contract-level `let x = e;` is an abbreviation,
and `let x: T where P;` is a per-clause existential that the callee chooses.
Neither one is a single value that the caller chooses for the whole contract,
and the reference refuses `let ... where` in memory segments "until Click has a
contract-wide witness environment".

### Proposal: extend instance binders instead of adding a parameter form

```click
extern uint64 strlen(const uint8* bytes) {
    views s: cstr_at(bytes, _);
    ensures result == s.len;
}
```

This needs three extensions, and each one generalizes an existing form:

1. A binder on a `views` clause, and on a fieldless resource. Today a binder
   requires `owns` and fields. A `views` binder names a borrowed instance,
   which the callee cannot change.
2. `_` in a binder's arguments. The bound instance fixes that argument; the
   clause does not.
3. `s.param` projects a resource parameter by name, just as `s.field`
   projects a field. A parameter that shares a name with a field is refused at
   the declaration.

**Meaning.** The callee is proved for every instance that matches
`cstr_at(bytes, _)`, that is, for every `len`, and the facts of the instance
are its premises. The caller supplies the instance:

- automatically, under the existing rule: exactly one held `cstr_at` agrees
  with every argument that is not `_`;
- explicitly, by naming its own instance: `views str: cstr_at(src, n);` and
  `{ s: str }`;
- or, new and needed only for (d), by naming a resource term,
  `{ s: cstr_at(src, n) }`, which binds the instance with those arguments.

**Later clauses.** A binder is bound before the clauses that follow it are
evaluated, so `s.len` may appear in `ensures` and in later memory segments:
`owns dst[0..s.len + 1u64];` and
`requires separate(memory(dst[0..32]), memory(src[0..s.len + 1u64]));`. This is
the contract-wide environment that the reference says `let ... where` lacks,
limited to values that a held instance determines. A clause may name only
earlier binders.

**`old(...)`.** A `views` instance cannot change during the call, so
`old(s.len)` is `s.len`. For an `owns s: cstr_at(p, _)` binder, `s.len` reads
the returned instance's argument and `old(s.len)` the entry instance's, the
same rule as for fields.

**Expansion.** Binding is part of the simple call rule: it is deterministic,
indexed by family and base, and involves no search, as today's automatic
binders do. A bare `step()` therefore stays valid expanded text.
`click expand` writes `{ s: name }` when the caller's instance has a name, and
writes the resource-term form when the call assembles the instance as in (d).

**Not an executable ghost.** Nothing is passed at run time. The C call, its
ABI and the C source are unchanged. `s.len` is a universally quantified
contract variable, and the call rule instantiates it with the matched
instance's argument value. The kernel needs no new concept: it already binds
instance identities at a call, and it binds the argument value the same way.

**Elsewhere.** Dafny ghost parameters are explicit arguments at every call.
They are erased at compile time and need ghost-ness rules because they live in
executable code. VeriFast's `requires [?f]string(s, ?cs); ensures result ==
length(cs);` binds pattern variables from the matched heap chunk. That is the
closest match: the binder with `_` is VeriFast's `?len`, but Click refuses an
ambiguous match instead of taking the first chunk, and it offers an explicit
map.

**Alternative A.** A contract quantifier,
`forall (len: uint64); views cstr_at(bytes, len); ensures result == len;`, reads
exactly like the stated goal. The caller would supply `{ len: n }`, or it
would be inferred when one held instance determines `len`. The cost is that
call maps gain a second namespace (values beside instances), and inference has
to decide which clause determines `len`. Under B the instance carries the value
and binding stays one rule. **Recommendation: B.** A remains open if bare
names are preferred.

### Kernel mechanism for (c)

Implemented as sketched here. The paragraph above assumed that the kernel binds the
argument value "the same way" it binds instance identities. It does not: a
binder today names an exclusive, field-bearing instance
(`CResource::Instance`), and `cell.field` is a kernel projection of that
instance's field by its identity. `cstr_at` is fieldless, so a clause
`cstr_at(bytes, len)` is an ordinary composite with no identity, and an
instance cannot be viewed at all (stable views, D12). Neither a field
projection nor an instance binding can carry `s.len`.

The smallest kernel concept that can is a value parameter of the C function's
own contract. `CFunctionContractInterface` already has one,
`value_parameters`, which named contracts and closure captures use:

- The surface elaborates `views s: cstr_at(bytes, _);` to a contract value
  parameter `s.len: uint64` and the ordinary clause
  `views cstr_at(bytes, s.len);`, and resolves `s.len` and `old(s.len)` to it.
  `s.p` for a written argument is that argument.
- The body is proved with the value parameter bound to a fresh value, as
  `contract_refinement_context_for_interface` already does for a named
  contract that no fact fixes: the contract holds for every `len`.
- A call binds it per call: from an explicit `{ s: cstr_at(src, n) }` or
  `{ s: str }`, or, when no map entry is written, by the kernel choosing the
  argument of the one held `cstr_at` whose written arguments agree, as
  `selected_call_binder_application` chooses a unique instance today. The
  choice is not trusted: the instantiated requirement is checked as any
  other.

This changes the kernel's call rule (per-call value arguments for a direct
call, today only fixed by a function-value fact) and the function entry
(fresh values for value parameters), and it touches certification, the
contract interface identity, expansion, and the import summary. The
maintainer approved this mechanism on 2026-10-15.

What landed:

- A `views` binder, or an `owns` or `consumes` binder with a `_` argument,
  is a value binder. An `owns` or `consumes` binder without `_` still names
  a field-bearing instance. Value binders are refused in named contracts.
- Declaration expansion names each `_` after the resource's parameter and
  appends `s.len` to the signature after the C parameters; the signature
  check compares only the C parameters, and lowering moves the value
  parameters back out of the kernel function's C parameters
  (`CFunction::with_trailing_value_parameters`).
- A proof entry binds the value parameters at fresh values beside the C
  arguments (`bind_c_function_arguments`).
- At a call, `call_value_arguments` takes each value from the one instance
  that agrees with the clause's other arguments: a term the call map names,
  otherwise a held instance found by the indexed shape-and-root candidate
  query. `{ s: str }` names the caller's own binder's clause. No instance, or
  two with different values, is refused; equal values are not searched for.
- `s` itself is a name for the clause, not an instance identity, so
  `{ s: str }` and `s.len` are the whole interface.
- A C library function's value binders, such as `strlen`'s `s`, are named
  in a program's call map too. The library is parsed apart from the
  sidecar, so the sidecar's parser asks the loaded library for the binders
  of a callee whose contract the library supplies
  (`library_c_function_value_binders`) when the sidecar declares none.

Mdtests: `cstr_at_binder_*`, `cstr_at_owned_value_parameter_keeps_its_length.md`,
and `cstr_at_call_map_*`.

## (d) Call-site assembly of a viewed composite

**Status.** Implemented for owned bytes by the kernel's existing composite
view adapter (`candidate_composite_view_adapter`): a caller that owns the
body's bytes and holds its facts, but no instance, has the call materialize
`owns R(a)` from those bytes, lend it as `views R(a)`, and recover the bytes
at return (`mdtests/cstr_at_call_assembles_a_view_from_owned_bytes.md`; the
refusal without the terminator fact is
`mdtests/cstr_at_call_assembly_needs_the_terminator_fact.md`, and names it:
"assembling `views cstr_at(src, n)` from owned pieces requires an exact body
fact", with the missing fact and the available facts, as a refused fold
reports them). The adapter
used to check the body facts by the refinement route only, which missed a
quantified fact the caller states under another binder; it now also accepts
the exact routes a fold uses. An owner of `cstr_at` lends it to a `views`
callee as before (`mdtests/cstr_at_owner_lends_its_string_to_a_viewing_callee.md`).
With the owning body this is the answer to "should assembly lend a body's
`owns` clauses as views": it does, from owned bytes.

Assembly from bytes the caller only views is deferred (maintainer decision,
2026-10-15) until a real proof needs it. The adapter
escrows an owned head; a caller holding `views src[0..n + 1u64]` has nothing
to escrow, and lending it `views cstr_at(src, n)` needs a ledger transition
that derives a composite description from a live view binding whose
description covers the body, the inverse of the existing projection. That is
a ledger change and needs approval.

The rest of this section is the original proposal, written for a
views-only body; the owned-bytes route above is what landed.

**Rule.** At a call whose callee requires `views R(a)`, all of `a` is known
once binders are resolved; under (c), from `{ s: R(a) }`. Assembly applies
when the caller holds no instance `R(a)`, folded, owned or viewed, and `R`
qualifies:

- it has no fields, resource parameters, `let` witnesses, guards or matched
  arms;
- it has no child resources (`owns Q(...)` or named children);
- its memory clauses are `views` only (`owns` clauses lent as views is a
  possible extension and an open question below), and its other clauses are
  pure `fact`s.

`cstr_at` qualifies.

**Steps.**

1. Instantiate `R`'s body at `a`, one level.
2. Lend each `views` segment from the caller's holdings through the existing
   plain-view loan, the one that serves a `views p[lo..hi]` requirement today:
   from owned, viewed, literal or static storage, including a covered
   subrange.
3. Check each fact in the caller's state at the call, as a precondition with
   the same obligation and the same failure. A proof may state it with `have`
   before the call.
4. The callee's entry receives `views R(a)` exactly as from a folded loan.
5. At return the plain loans return as they do today. No `R` instance
   persists in the caller.

**Soundness.** Assembly is the existing `fold(R(a))` before the call and
`unfold` after it, performed by the call rule. A fold of a views-only body
checks the same facts against the same views, and unfolding a viewed instance
recovers exactly the loans it took. The callee sees what a folded instance
would give it: read access to the instantiated segments and the facts. The
lent bytes are shared-borrowed for the whole call, so the caller cannot write
them, the callee can only read them, and every memory fact checked at the call
stays true until the loan returns. The loan accounting is the existing
plain-view lending, unchanged. Assembly is never tried while a matching
instance is held, so it cannot duplicate an instance or shadow one.

**Cost.** Assembly runs only on a miss for an exact instance. It processes the
fixed clause list of one body: for `cstr_at`, one symbolic range
`p[0..len + 1]`, lent as one range with no per-byte work, and four facts
discharged as requirements. Nothing depends on the string's length, on
unrelated resources, or on proof history, and with no children there is no
recursion. Selection uses the existing indexed resource lookup by family and
base.

**Diagnostics.** A failure names the requirement and the assembly step:

- "call to `strlen` needs `views cstr_at(src, n)`; the caller holds none, and
  assembling it needs `views src[0..n + 1u64]`, which the caller does not
  hold";
- the unclosed fact, as a refused fold reports it, "requires an exact body
  fact `src[n] == '\0'`";
- for a body that does not qualify: "`R` cannot be assembled at a call: its
  body has child resources; fold it before the call".

**Not proposed.** A persistent fold, which would change the caller's state
invisibly; recursive assembly through children, whose cost grows with the
structure; assembly for `owns` or `consumes` requirements.

## Migration plan

PR A landed the owning body, the `views`/`owns`/`consumes`-`produces`
choice, the terminator mdtests, and assembly from owned bytes. Its second
increment landed step 1. PR B landed steps 3 to 6. The viewed-bytes half of
step 2 is deferred.

1. Done: (c), `views` and fieldless binders, `_`, `s.param`, the
   resource-term map entry, with ambiguity, missing-instance and unheld-term
   refusals, an `owns` binder with `old(s.len)`, and a later memory segment
   that names `s.len`.
2. Implement (d) from viewed bytes, with positive, missing-view, failed-fact
   and non-qualifying-body mdtests, and a scaling regression that grows
   string length and unrelated held resources.
3. Done: the `strlen` library contract is
   `views s: cstr_at(bytes, _); ensures result == s.len;`, switched in one
   step. It needs a held string, not only `viewable`, which deliberately
   strengthens the precondition. The 29 mdtests that mention `strlen`
   migrated as follows:
   - Declaration and binding tests keep their shape; the ones that verify a
     call view `cstr_at(s, _)` and ensure `result == str.len`.
   - Callers whose subject was the call (`<string.h>`, redeclaration,
     return and copy forms, identity casts, plain and signed `char`
     forwarding, reordered clauses, the empty-string catalog test) view
     `cstr_at(p, _)` or `cstr_at(p, n)`. Offset, missing-requirement and cast
     refusals now report the missing string. The write refusal owns the
     string and unfolds it to write, so the call finds no instance.
   - `cstr_readable_witness_stated_before_call.md` owns its three bytes and
     states the string's facts with `have` before
     `step(strlen(bytes), { s: cstr_at(bytes, 2u64) })`, which assembles the
     string.
   - The transport tests keep their `string::readable` witnesses and
     transports: the positive ones add the viewed string the call uses, the
     refusals that fail before the call are unchanged, and
     `cstr_dynamic_indexed_read_requires_permission.md` and
     `cstr_dynamic_invalidated_transport.md` hold only the predicate and
     show that the call refuses it.
   - `stdlib_every_symbol.md` needed no change.
4. Done: in `examples/label-build-flags`, `label_measure` and `label_copy`
   take `views s: cstr_at(src, _)` and state exactly the kept length,
   `s.len < 32u64 implies result == s.len` and
   `32u64 <= s.len implies result == 31u64`, which `label_fit` now states
   too. `label_copy` requires
   `separate(memory(dst[0u64..32u64]), memory(src[0u64..s.len + 1u64]))`,
   opens the string to lend `memcpy` its prefix, and keeps
   `dst[result] == '\0'`. The obtain-and-transport proof became
   `step`s, a `with` and `step_until(function.exit)`. With M3 the contract's `owns` and
   `views` already keep `dst` and the string apart, so the `separate` is
   implied; it stays, unchanged. The copied bytes are stated too (2026-10-16):
   `ensures bytes::equal(dst, 0u64, src, 0u64, result)`, proved by marking
   the point after `memcpy`, stepping over `dst[n] = '\0'`, and transporting
   the unfolded postcondition to a `have` over `n`. Three gaps between that
   proof and the verifier were found with M3; the first two were fixed then:
   a bare `transport` in a `have` selects its premises at the frontier the
   `have` was opened on (`mdtests/bare_transport_inside_have.md` now uses
   `close()` for the unchanged read), and a
   `char *` argument to `bytes::equal`'s `uint8[]` parameters unfolds to the
   same `uint8` reads as `memcpy`'s postcondition
   (`mdtests/char_argument_to_byte_predicate_unfolds_as_bytes.md`). The third
   was first recorded as the frame across `dst[n]` needing `k != n` from the
   guard. That reading came from a supplemental memory-history walk, which
   runs without the proof context's facts; the checks that run with the
   guard `k < n` assumed already crossed the store. The actual causes were:
   - `transport using` required the call's quantified postcondition
     verbatim, and the written source names its own binder; it now accepts a
     binder-renamed quantified premise, as `apply using` does;
   - the checked quantified frame took only `int32` binders; it takes every
     C integer binder, here `uint64`;
   - the outcome goal of a contract with resource claims unfolded a `char *`
     argument textually, reading `(int8)` bytes; it now takes the byte view
     as `unfold` and `have` goals do;
   - for the smart closer, a premise that is one conjunct of a source fact's
     lowering (the `separate` clause beside its well-formedness conditions)
     had no spelling; it is now spelled by that whole source fact;
   - over `unsigned char` buffers with 32-bit-bounded ranges, the read
     `src[k]` had no typed range membership for a `uint64` index; one exact
     order fact `k < c` now places it.

   `mdtests/memcpy_then_terminator_keeps_copied_bytes.md` and
   `memcpy_then_terminator_keeps_copied_unsigned_bytes.md` keep the
   pattern; `a_store_inside_the_copy_does_not_keep_copied_bytes.md` refuses
   a store at `dst[n - 1]`. A smart `close()` proves the claim stated over the
   count but not over `result`, which only function exit can name
   (`copied_bytes_through_result_need_an_explicit_transport.md`).
5. Done: in `src/surface/tests/expansion_tests.rs`, the `read_terminator`
   fixture views `cstr_at(haystack, _)` among the reordered clauses and
   still asserts that no hidden planning transitions occur. It is not an
   assembly fixture, since assembly from viewed bytes is deferred.
6. Open. The strlen-shaped tests in `src/surface/proof/surface_synthesis/tests.rs`
   synthesize the guarded quantified `loadable` carrier of
   `string::readable`, which no longer depends on `strlen`. Revisit them with
   M3: rename them to C-string shapes if `memcmp`'s guarded `defined` range
   still produces that carrier, otherwise retire them.
7. Done: M3, `memcpy` views its source and `memcmp` both operands, and
   the explicit `separate` left `memcpy`'s contract.

## Open questions for the maintainer

Decided on 2026-10-15: B (the instance binder, `s.len`); the resource-term
map entry `{ s: cstr_at(src, n) }` is accepted; an owner lends its body's
`owns` clauses as views; the body owns its bytes. (c) is built on per-call
value parameters of a C function's contract, as sketched in
[Kernel mechanism for (c)](#kernel-mechanism-for-c). Assembly from viewed
bytes is deferred until a real proof needs it.

Decided on 2026-10-15: `strlen` switches in one step.
