# Shared-heap-graph source probe

This is the source-selection checkpoint for the P1
[shared-heap-graph demo](../../issues/shared-heap-graph-demo.md), not a Click
verification example yet. The synthetic
[`shared_parent.c`](shared_parent.c) is ordinary sequential C fixed before its
contracts and resource rules are written. It stays here until Click can verify
it; adding an unproved directory under `examples/` would make the normal
example gate fail. Later example work must use these bytes, not reshape the C
to expose a friendlier proof state.

## Selected profile

| Boundary | Selection |
| --- | --- |
| Language and target | C11, x86-64 Linux, LP64, eight-bit bytes and `-funsigned-char`. Default Click target (no sidecar `target` directive); the kernel/user-space distinction is irrelevant to this sequential `malloc`/`free` program. |
| Compiler and C library | Pinned only to the extent Click's C0 models `malloc`/`free`, `int32`, and struct assignment. No system headers are included; like `examples/refcount`, the probe relies on Click's predeclared `int32`, `malloc`, and `free`. |
| Shape | One `struct child { int32 refs; int32 payload; }` with a single branch-on-count `child_release` (final `free` vs nonfinal decrement in one body — the issue forbids splitting these into proof-selected entry points), plus `struct parent { struct child* kid; }` with attach/read/detach helpers and two pipelines covering both destruction orders. Allocation-failure paths release only acquired resources and return `-1`. |

Native syntax-only smoke (Click supplies `int32`, `malloc`, `free`; flags only,
source unchanged):

```sh
clang -std=c11 -Dint32=int -include stdlib.h \
  -Wall -Wextra -Werror -fsyntax-only design/shared-heap-probes/shared_parent.c
```

## Frozen program

`child_init` establishes the creator reference (`refs == 1`). Each pipeline
attaches the child to two parents (`parent_attach` stores the pointer and
retains), drops the creator reference, destroys one parent, reads the payload
through the survivor (`parent_read_payload`), destroys the remaining parent,
and frees both parent structs. Success returns the payload; any allocation
failure returns `-1` after releasing what was acquired.

The future Click proof must show the payload read is valid with the specified
value, the child is freed exactly once, both destruction orders discharge all
allocation obligations, and the negative regressions in the issue fail for
their intended local reasons. A native compiler run checks C syntax only; it
does not establish any ownership property.

## Frozen-source helper checkpoint, 2026-09-23

[`shared_parent.click`](shared_parent.click) now verifies all six helper bodies
against these unchanged C bytes: `child_init`, `child_retain`, `child_release`,
`parent_attach`, `parent_read_payload`, and `parent_detach`. Run
`click verify design/shared-heap-probes/shared_parent.click` to check them.
This is a helper checkpoint; neither `run_first_destroyed` nor
`run_second_destroyed` is selected by that sidecar yet.

A scratch proof of `run_first_destroyed` advances through both detaches and
both parent frees, discharging all resources. The read helper now promises its
`link.link` model is unchanged. At the caller, an explicit `rewrite` combines
that promise with the pre-read `Linked(kid)` fact, so the second detach selects
the held `child_ref(kid)`. Detach returns ownership of `&p->kid` after setting
it to zero, allowing the parent allocation to be freed. These are helper
contract improvements; the full caller proof is not in the sidecar yet.

The remaining success-path goal is `out == payload`. The verified helper
contracts now promise payload preservation through `child_retain`, the
nonfinal branch of `child_release`, and `parent_attach`. Attach requires
`separate(memory(&p->kid), memory(kid->payload))`, since it stores the link.
`parent_detach` still has no payload-preservation promise, so the full caller
cannot carry the initialized value through its first detach.

The new pointer-base `rewrite` closes the precise snapshot gap inside detach.
After stepping across `kid = p->kid` and the `child_release(kid)` call, an
explicit rewrite with `kid == at(statement(2).entry, p->kid)` proves
`at(statement(2).entry, kid->payload) == old(kid->payload)`. With a stated
separation condition between the parent link cell and child payload, the
proof also carries the guarded payload equality across `p->kid = 0`.

The next blocker is contract certification, independent of that equality:
adding even the tautological `ensures old(p->kid) == old(p->kid)` to the
frozen `parent_detach` makes exact symbolic execution report that it cannot
prove `child_ref`'s declared refcount fact at return from `parent_detach`.
This occurs after the nested `child_release` call; the same helper body
verifies without the pure `ensures`. A focused regression should add that
trivial postcondition to a branch-on-count release caller and expect
certification to pass. Repair this certification boundary before adding the
guarded detach guarantee and proving `out == payload`.

An indexed `child_ref(obj, payload)` resource was also tested; its contract
cannot choose `payload` by reading `obj->payload` before ownership is granted,
and contract witness lets are not supported in `owns` clauses. Neither probe
changes the frozen C.

## Reduction findings, 2026-09-17

Reduced against the frozen machinery with scratch sidecars (kept in
`reduction/`). The goal was to decide whether the milestone needs a new
resource-language primitive, as the issue asks, or whether existing counted
populations and composites suffice.

### What works (verified)

A **companion encoding** avoids nesting the child capability inside the
parent:

```click
resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}
```

`parent(p)` owns only the link cell; each parent carries one **top-level**
`child_ref(kid)` unit, tied to its parent by the `p->kid == kid` fact. With
this shape, all of the following verify under the normal engine:

- `child_init` (fold the unit), `child_retain` (`open`, execute),
  `child_release_nonfinal` (`open`, memory bound `1 < obj->refs`),
  `child_release_final` (`unfold`, free);
- `parent_attach`: `p->kid = kid`, retain the unit, then
  `fold(parent(p), { link: ParentLink::Linked(kid) })` **before** the retain
  call (`execute_until(statement(1))`). Folding the link *after* a call was
  not closable (see gap 3);
- `parent_read_payload`: `unfold(link)`, `open(child_ref(kid))` to expose the
  child object, read `kid->payload`, then refold the link;
- a complete single-parent `pipeline` (init, attach, read, detach, final
  release, return payload) in `reduction/full.click`.
- a link-only parent fold (`consumes p->kid; produces parent(p)`) with no
  population in play.

### What does not work, and the boundary

1. **Nesting a memory-bearing counted family in a child slot is unsupported.**
   A composite declared `contains child_ref(p->kid)` cannot be `unfold`ed
   (`resource rewrite changed more than a definitional representation`) or
   `open`ed (`resource rewrite produced an unchecked pure-fact delta`). Named
   carriers are also refused: `owns held: child_ref(kid)` in a match arm hits
   `named child resources currently require a constructor match arm` /
   `resource \`child_ref\` has no fields; use ordinary unnamed ownership` /
   `resource match children require named exclusive ownership`. The reference
   documents the rule: "Memory and token families in a child slot ... remain
   unsupported" (`docs/reference/language/index.md`). The companion encoding
   above is therefore not optional; nesting is not the path.

2. **The milestone's single branch-on-count `child_release` does not yet
   verify.** `reduction/rel.click` gives one contract to
   `if (obj->refs == 1) free(obj); else obj->refs = obj->refs - 1;`:
   - `consumes child_ref(obj)` alone leaks the allocation on the nonfinal path
     (`LiveAllocationLeak`), because the model reads a lone `consumes` as
     "population is one and is gone";
   - `owns child_ref(obj); consumes child_ref(obj);` instead fails the final
     path with `missing resource fact owns child_ref(obj)`.
   There is no single linear contract that covers "consume the last unit and
   free" versus "consume one of many". The existing refcount example sidesteps
   this by using two C entry points (`object_release_nonfinal` /
   `object_release_final`), which the issue explicitly forbids. This is the
   real reducer: Click needs a checked conditional-release shape (an effect
   keyed by whether the population was one, or a way to state "consume the
   final unit and release its allocation" in one contract).

3. **A load fact does not survive a call for the next frontier.** In
   `parent_attach`, folding the link after `p->kid = kid; child_retain(kid);`
   fails to re-establish `p->kid == kid`; folding first, before the call,
   works. The call touches a different object, so this is a frame/load-identity
   gap, not a soundness result.

4. **Field-bearing composites can only be reopened by unfold/refold, not
   scoped `open`.** `open(parent(p))` is refused ("has fields; bind it with
   `owns name: ...`") and `open(link)` does not parse, so the read shape is
   `unfold` ... `fold`.

5. **Population arithmetic bookkeeping.** `owns X; produces X` (net +1) on a
   function that also folds a composite left an unproved `resource population
   invariant` VC (`count == 2`); the equivalent `consumes X; produces X` (net
   0) verified. A `requires 1 < count(child_ref(obj))` release left a
   `returned resource quantity fits post-population` VC, while the memory form
   `requires 1 < obj->refs` verified.

### Next chunk

Adopt the companion encoding (it verifies for the read/retain/detach
direction) and fix gap 2 first: give a branch-on-count release one checked
contract. Gaps 3 and 5 are the next reducers; gap 1 is documented and avoided.
No issue is filed; this note is the record.
