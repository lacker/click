# Click resources and Rust borrowing

Investigation requested on 2026-09-11, against Click commit
`bf0399b53f02c4808461ae722390cd88b0aa88bf`. This is a design investigation,
not an implemented Rust or C++ frontend or a change to the rbtree launch
roadmap. The accompanying [probes](borrow-probes/README.md) record executable
evidence and reproduction commands.

## Assessment

The analogy between Click `owns`/`views` and Rust `&mut`/`&` is useful and
close at ordinary function-call boundaries. Keep the two access modes. A
literal identification of the current memory resource laws with Rust
references would nevertheless be incorrect.

The central missing concept is a borrow protocol: which authority is lent,
which accesses the lender must suspend, how that authority can be reborrowed,
and when the lender can recover it. This is a promising extension around
the current resource system, not evidence that the resource system must be
replaced. Its adequacy for unsafe Rust still requires a separate investigation.

The earlier advice to separate storage, validity, and access should not be
read as a proposal to replace `owns` and `views` with three competing resource
systems. Click already separates allocated storage and initialization from
memory-access authority. Rust references can package the relevant facts and
authority together while the checker retains those distinctions internally.

## What the current implementation actually guarantees

The [resource documentation](../docs/concepts/resources.md) and
[memory resource algebra](../src/kernel/primitives/resource_algebra.rs) agree:

- Memory ownership permits reads and writes. A memory view permits reads.
- Ownership entails a viewed core without surrendering write authority.
- Views can coexist with an overlapping owner. A view does not freeze the
  memory contents against writes by that owner.
- A memory write changes the current snapshot. A prior observation remains
  a fact about its prior snapshot unless checked framing transports it.
- Ownership can satisfy a callee's view requirement for the duration of a
  call without leaving a persistent caller view afterward.
- `owns` borrows and returns the resource selected at function entry;
  `consumes` and `produces` express other transfer roles.

The algebra's `pair_validity_error` checks overlapping owned ranges; it
does not reject an owner/view overlap. Its `memory_resource_fact_permits_write`
checks the address range, width, and owned authority. It does not distinguish
two Rust borrow origins for accesses to the same address.

These are intentional, useful C semantics. The existing
[`pointer_params_may_alias_without_separate` regression](../mdtests/pointer_params_may_alias_without_separate.md)
rejects an unchanged-value claim after a potentially aliasing write. It
passed when rerun during this investigation, meaning the false claim was
correctly rejected.

The new [C probe](borrow-probes/alias.c) writes 7 through `p` and then reads
through `q`. Its sidecar owns `p`, views `q`, and requires `p == q`. Click
verified `result == 7` using ordinary verification. This is positive evidence
that a current view can observe an owner's mutation, not a Click soundness bug.

## Where the Rust analogy holds and where it needs more structure

| Situation | Relationship to Click |
| --- | --- |
| A helper reads through `&i32` and returns | Close to a call-scoped `views` requirement satisfied from ownership. |
| A helper mutates through `&mut i32` and returns | Close to `owns`, with exclusive access lent for the call and returned afterward. |
| A shared borrow remains usable across a write | Requires restricting the writer. Current memory `views` does not do this. |
| A mutable reference is reborrowed | Requires tracking a child borrow and restricting the parent until it can be used again. |
| A function returns a borrowed reference | Borrow obligations survive the call; returning all entry authority at function return is insufficient. |
| `&Cell<i32>` supports a mutation | Shared access needs a type-specific protocol, not a universal read-only view of all underlying bytes. |
| `&mut MaybeUninit<i32>` is initialized | Ownership and wrapper validity can exist before the payload is a valid `i32`. |

Rust's reference validity and aliasing rules apply even in unsafe code.
The Rust Reference explicitly leaves some details of unsafe aliasing unsettled.
An implementation must identify its supported model and compiler assumptions;
passing the safe borrow checker is not evidence that arbitrary unsafe accesses
have been justified. [Rust Reference](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)

## The decisive distinction: projecting a view versus lending authority

For today's memory resources, the schematic rule is:

```text
own(R) entails view(R), with own(R) still usable
```

That supports a read-only operation within a context that can also write.
For a shared Rust borrow of an ordinary integer, the protocol instead needs
something like:

```text
exclusive authority over R
    -> suspended lender authority + shared borrow of R for lifetime k

end k, after its active accesses and dependent borrows are finished
    -> restored lender authority over the current R
```

This is explanatory notation, not proposed Click syntax or checked rules.
Reborrowing needs a dependency relation between the child and parent loans.
The lender retains an entitlement to recover authority, not a second usable
writer during the loan. A mutable child loan must also restrict conflicting
parent reads, not only writes.

Duplicability is compatible with this design. A shared-borrow description can
be copied while every actual access additionally requires evidence that its
lifetime is active. Ending the lifetime can invalidate that access evidence
without searching for and deleting every historical copy of the description.
Plain fractional permissions alone do not supply this lifetime protocol.

RustBelt supplies a useful precedent: it separates type ownership from a
type-specific sharing predicate, and uses lifetime tokens to control access
to borrowed resources. Shared-reference descriptions can be persistent while
access remains lifetime-bound. Its treatment of `Cell` and mutexes shows why
the sharing interpretation depends on the type.
[RustBelt, sections 4–6](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)

VeriFast provides a concrete implementation reference: its lifetime logic
ends a lifetime before recovering exclusive ownership from a borrow.
[VeriFast lifetime logic](https://verifast.github.io/verifast/rust-reference/lifetime-logic.html)

## Three specific complications to test before selecting the rules

### Returned references and functional specifications

The `left` probe returns a mutable reference into a caller's `Pair`. A
caller can mutate through that result and later use the pair. It cannot
mutate `p.left` while the returned reference remains in use; the negative
probe receives Rust diagnostic E0506.

A future contract must connect the returned reference, its parent loan, and
the value recovered by the caller after the loan ends. Current snapshots and
explicit memory may help describe this, but the current return boundary alone
does not establish that connection. Experiment with a conditional choice of
borrowed fields next, so a solution cannot depend on one fixed field path.

RefinedRust addresses this with borrow names connecting a mutable reference's
current value to what its owner recovers later. Its frontend also extracts
lifetime hints alongside MIR. This is evidence that both semantic contracts
and compiler extraction need attention, not a reason to introduce prophecy
variables into Click without testing whether its explicit-memory design needs
them. [RefinedRust, sections 2–5](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf)

### Interior mutability

The positive Rust probe calls `Cell::set` through one shared reference and
observes the update through another reference to the same cell. Both references
remain ordinary shared references. Rust's `UnsafeCell` is the primitive behind
this exception to shared-reference immutability; it does not remove the
uniqueness requirements of mutable references.
[UnsafeCell](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html)

Keep `views memory(range)` read-only. A shared view of an abstract Rust object
would expose its allowed operations through that type's checked sharing
protocol. `Cell`, `RefCell`, and `Mutex` require different protocols; simply
projecting every contained owned byte range to a memory view is insufficient.
Do not authorize arbitrary writes merely because a type contains `UnsafeCell`.

### Address identity and access authority

Two pointers can identify the same storage while having different allowed
accesses during a Rust borrow. Current C checks can transfer range authority
across proved pointer equality. That behavior should remain correct for C,
but Rust needs additional access-origin checks.

The future representation should keep storage identity usable for load/store
indexing while tracking reference/loan provenance separately. Whether that
information belongs on pointer values, execution operations, or both is an
open implementation decision. It must not be erased by casts or equality
rewrites in the unsafe subset. Allocation provenance alone is insufficient.

## What the compiler probes tell us

The Rust probes compile and run for shared-then-write, mutable reborrowing,
returned field borrowing, disjoint slices, `Cell`, initialization, and cleanup
on both early and ordinary returns. Three conflicting-write probes fail with
E0506. These are concrete compiler/runtime observations, not formal proofs.

One especially useful result: in unoptimized MIR for `shared_then_write`,
the write through `p` occurs before `StorageDead(q)`. The shared reference's
last use is earlier. Therefore local storage lifetime cannot simply serve as
borrow lifetime. The default MIR output also removes the child reference in
`mutable_reborrow`, while unoptimized MIR retains it. A production frontend
must select its MIR phase and collect loan/lifetime information deliberately.
Human-readable dumps are inspection tools, not stable interchange formats.

The C++ probe permits `int&` and `const int&` to alias while the first writes
and the second reads. Its RAII guard executes on both returns. Clang's CFG
dump includes an implicit destructor on each return path. Thus C++ needs
cleanup and object-lifetime semantics, but its references do not require
imposing Rust's exclusive/shared borrow discipline on all C++ accesses.

The compiler probes use the local ARM64 macOS target; the Click probe uses
Click's supported x86-64 Linux target. They establish structural semantic
distinctions, not cross-target layout agreement or source-to-machine refinement.

## Changes worth making now

1. Retain `owns` and `views`, and document that a current memory view grants
   read access without preventing an overlapping owner from writing.
2. Preserve the existing separation of access mode, transfer role, and
   snapshot in `CResourceSpec`. These are already separate fields; no broad
   refactor is needed to create that separation.
3. Continue the P1 work on supported observations and scoped call borrows.
   Its support/version/scope boundary is useful groundwork, but is not yet a
   full Rust loan system. Do not broaden that issue's semantics silently.
4. Preserve a place for access-origin and loan checks beside storage lookup
   when changing memory-access interfaces. Implement them when the proposed
   borrow rules and their regressions are concrete.

Do not redefine all C views as freezing borrows. That would reject valid C
and the positive probe. Do not call a mutable reborrow a duplicable owner.
No evidence from this investigation warrants replacing the resource algebra
or delaying rbtree for a production second-language frontend.

## Next investigation and decision gates

The next bounded experiment should exercise a checked borrow protocol before
spending effort on broad parsing support:

1. Specify and check shared loans, mutable reborrows, end-of-loan recovery,
   returned loans, and branch-selected field loans. Include negative cases
   for parent reuse too early, use after expiry, and duplicate recovery.
2. Test one interior-mutable object protocol and one unsafe raw-pointer
   access against a selected Rust aliasing model. Distinguish unsupported
   behavior from an invalid proof. Do not infer general unsafe Rust support
   from the safe examples.
3. Compare compiler extraction phases using those same inputs. Preserve
   source locations, loan relationships, initialization, and cleanup effects.
4. Check deterministic scaling with several loan counts and nesting depths,
   plus growing unrelated resource contexts. Ending a loan should touch its
   dependent obligations, not scan every fact, pointer, or memory snapshot.

A minimal Rust frontend is justified if it lets these unchanged sources drive
the same kernel checks more faithfully than manually constructed operations.
A minimal C++ frontend should similarly earn its place with real implicit
cleanup. Parsing scalar arithmetic in a new syntax would not resolve the
resource question. The resulting decision should state which laws are shared,
which are language-specific, what remains assumed, and which changes belong
before versus after the rbtree launch.
