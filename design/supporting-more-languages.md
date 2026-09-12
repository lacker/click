# Supporting more languages

This is the durable design reference for extending Click beyond C. It
consolidates the C++/Rust architecture and borrowing investigations requested
on 2026-09-11. Initial borrowing evidence was recorded at `bf0399b5`; this
consolidation uses `2ac83e6d`. The [probe record](borrow-probes/README.md)
contains executable evidence, compiler versions, and reproduction commands.
No C++ or Rust verification frontend is implemented by this document.

The implementation backlogs are the P1
[stable views issue](../issues/fix-views.md) and P1
[basic C++ support issue](../issues/basic-cpp-support.md). They own current
acceptance criteria. This document owns the cross-language rationale and
future investigations, so those decisions survive the eventual issue closures.

## Sequence: C++ first, Rust next

Deliver basic C++ first: a pinned, non-throwing C++20 subset with scalar
functions, pointer/reference parameters, simple objects, explicit construction,
and implicit destruction on ordinary and early returns. The defining example
is an RAII guard that restores a caller's integer after the function captures
its return value. This supplies a real language-specific semantic test and a
usable path from original `.cpp` source through normal Click sidecars.

| Consideration | C++ first | Rust first |
| --- | --- | --- |
| Compiler boundary | Clang semantic AST and control flow; a new typed exporter is needed. | rustc MIR plus the selected phase's type, move, borrow, lifetime, and drop information. |
| Small meaningful feature | References and a simple constructor/destructor across two return paths. | Shared/exclusive references and reborrows across calls. |
| Existing overlap | Much of the scalar, pointer, memory, and call machinery can be reused after checking C++ semantics. | Memory/call machinery can be reused, but reference validity and borrow provenance need additional interpretation. |
| Main design question tested | Can a second frontend preserve source identity, object lifetime, and implicit cleanup in the shared checker? | Can the borrow protocol and compiler extraction agree on active references and recovered authority? |
| Work already being done without a frontend | C++ cleanup still needs an end-to-end source witness. | `fix-views` already requires small checked borrowing and concurrency models. |

This is a sequencing judgment, not a measured claim that a Clang exporter is
cheap. Today Click's compiler import captures preprocessed C text; it does
not already import Clang ASTs. C++ first limits the new semantic work while
testing the whole program-language boundary. Rust follows once the shared
borrowing model and that boundary have evidence behind them. Avoid doing both
frontends simultaneously for the first milestone.

The bounded C++ slice is P1 by explicit user direction. The launch remains
P1 -> unchanged Linux rbtree verification -> public launch with rbtree as the
key demo. Broad C++ coverage and Rust are later work. Neither a successful
compiler probe nor accepting C-shaped code with a `.cpp` extension is enough
to announce the first slice as complete.

## Shared architecture and source boundaries

Keep one Surface Click proof language and one checked verification engine.
Put new program-language frontends beside `src/languages/c`, as anticipated
by the [architecture](../docs/internals/architecture.md). Share the proof
object, logical terms, resources, memory operations, and tool orchestration
where their semantics agree. Retain a language-specific layer for validity,
aliasing, object lifetime, cleanup, and exceptional behavior.

The immediate implementation boundary is `C0VerificationSession` and its
prepared inputs in `src/surface/verification.rs`, not a repository-wide rename
of every `C`-prefixed type. Introduce a program/source identity and a small
semantic input boundary as the second frontend needs them. New rules must
advance the same checked proof object and carry ordinary provenance; do not
create a parallel verifier for a new source language.

Use compiler semantic information deliberately:

- **C/C++:** a pinned Clang LibTooling exporter can provide resolved
  declarations, types, layouts, source locations, and implicit operations.
  The first C++ exporter should own a narrow, versioned output schema.
  Clang's AST preserves source-level structure, and LibTooling supports
  standalone semantic tools. Human AST/CFG dumps are investigation aids.
  [Clang AST](https://clang.llvm.org/docs/IntroductionToTheClangAST.html),
  [LibTooling](https://clang.llvm.org/docs/LibTooling.html)
- **Rust:** use a pinned rustc integration around MIR, collecting borrow and
  type information deliberately before relevant information is erased.
  The compiler's borrow analysis includes moves and region inference over
  the control-flow graph. A pretty-printed MIR file alone is not the contract
  for the importer. [rustc borrow checking](https://rustc-dev-guide.rust-lang.org/borrow-check.html)

Do not choose optimized LLVM IR as the only source-verification boundary
because both compilers emit it. LLVM has its own undefined-behavior semantics,
including poison and undef; a proof of lowered instructions does not by itself
recover the source's type/reference/object-lifetime obligations. An LLVM
backend could be a separate future verification layer with an explicit
refinement story. [LLVM UB manual](https://llvm.org/docs/UndefinedBehavior.html)

Every prepared program must name its source language/standard, compiler and
exporter identity, target ABI/layout, semantic flags, selected sources, and
dependencies. Extend the current locked-import discipline; do not mix
certificates or cached successes across these identities. Start with one
qualified profile rather than making general multi-target support a hidden
dependency. The compiler and source-to-kernel translation remain in the
trusted computing base until a checked refinement replaces that assumption.
Smart proof search remains outside it.

For eventual mixed-language programs, keep allocation and address identity
shared across a real FFI boundary. Give each boundary an explicit calling
convention, layout, ownership transfer, validity, and unwind policy. Separate
language heaps that accidentally forbid cross-language aliasing would obscure
the problem. Cross-language calls and machine-code correctness are later
claims, not implied by two independent frontends.

## Control flow, goto, and implicit cleanup

The current statement-tree/frontier representation must grow beyond a cursor
that only advances through lexical source. The
[goto issue](../issues/goto.md) owns explicit C jumps; its design should also
accommodate C++ scope exits and Rust MIR blocks. A common edge representation
needs an explicit target, path state, source attribution, and any checked
scope/lifetime effects. A source jump, destructor call, loan expiration, and
object-lifetime end are distinct events.

For C++, leaving a scope can destroy constructed automatic objects, in reverse
construction order. Jumping into a scope across non-vacuous initialization is
restricted. The frontend supplies language-specific legal edges and cleanup
obligations; a shared label mechanism must not invent C++ semantics for C.
[C++ scope transfers](https://eel.is/c++draft/stmt.dcl)

Return has a sequencing requirement: first evaluate/capture the result, then
perform the required cleanup, then deliver the result and resulting state to
the caller. Otherwise a destructor changing an aliased location can silently
change the modeled return value. [C++ returns](https://eel.is/c++draft/stmt.return)

For Rust, MIR supplies explicit branches, drops, and unwind successors; drop
elaboration accounts for whether a value was actually initialized or moved.
Do not treat every local as needing an unconditional drop, or recover a loan
merely because its local storage ends. Future unwind/abort paths must be
distinguishable from normal returns. [rustc drop elaboration](https://rustc-dev-guide.rust-lang.org/mir/drop-elaboration.html)

The first C++ slice only needs normal scope exits and returns. General goto,
irreducible control flow, exceptions, Rust panic unwinding, and coroutines can
remain unsupported while the edge representation reserves their semantic
distinctions. Backedges still need invariants and termination evidence; a
tactic budget is not a termination proof. Compare a forward C cleanup jump,
the C++ RAII return example, and a Rust conditional drop when selecting the
shared representation.

## Shared resources and Rust borrowing

The P1 [views issue](../issues/fix-views.md) recommends stable shared borrowing
for ordinary memory. It supersedes the original investigation's advice to
preserve weak C views. The implementation observations below describe the
investigated baseline, not a requirement to retain it.

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

### What the investigated C implementation guarantees

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

These are the current sequential C semantics. The existing
[`pointer_params_may_alias_without_separate` regression](../mdtests/pointer_params_may_alias_without_separate.md)
rejects an unchanged-value claim after a potentially aliasing write. It
passed when rerun during this investigation, meaning the false claim was
correctly rejected.

The new [C probe](borrow-probes/alias.c) writes 7 through `p` and then reads
through `q`. Its sidecar owns `p`, views `q`, and requires `p == q`. Click
verified `result == 7` using ordinary verification. This is positive evidence
that a current view can observe an owner's mutation, not a Click soundness bug.

### Where the Rust analogy holds and where it needs more structure

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

### Projecting a view versus lending authority

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

## Borrowing complications to revisit for Rust

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

A mutex-like sharing protocol grants the right to acquire a guard; it does
not expose permanent raw views of its mutable payload. The invariant holds
the payload's authority between critical sections. A copied abstract view is
not automatically transferable between threads: type-specific sharing must
justify that transfer, including Rust's `Send`/`Sync` distinctions. Keep a
thread-local cell and a transferable mutex as contrasting model examples.

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

The proposed first C++ regression in
[basic-cpp-support.md](../issues/basic-cpp-support.md) adds an explicit
constructor and a destructor that restores the entry value. A temporary
header-free compiler probe returned 7/9 on the early/ordinary paths and left
the caller's integer at 41 in both cases. It compiled and ran with the same
Apple Clang 16 toolchain. Cross-target syntax/CFG inspection for x86-64 Linux
also showed the initializer list and both implicit destructor calls.
This checks the proposed example and compiler visibility, not a Click proof
or completeness of the future exporter. The original C++ probe uses host
headers; the new header-free reduction avoids treating host-header success
as Linux target qualification.

The compiler probes use the local ARM64 macOS target; the Click probe uses
Click's supported x86-64 Linux target. They establish structural semantic
distinctions, not cross-target layout agreement or source-to-machine refinement.

## Near-term decisions

1. Retain `owns` and `views`, but change ordinary memory views to stable
   shared borrows under the P1 [fix-views plan](../issues/fix-views.md).
   Until that lands, document the weaker current semantics accurately.
2. Preserve the existing separation of access mode, transfer role, and
   snapshot in `CResourceSpec`. These are already separate fields; no broad
   refactor is needed to create that separation.
3. Continue the P1 work on supported observations and scoped call borrows.
   Its support/version/scope boundary is useful groundwork, but is not yet a
   full Rust loan system. Do not broaden that issue's semantics silently.
4. Preserve a place for access-origin and loan checks beside storage lookup
   when changing memory-access interfaces. Implement them when the proposed
   borrow rules and their regressions are concrete.
5. Deliver the P1 basic C++ slice through a typed compiler import and checked
   cleanup edges. Share this edge design with goto without waiting for full
   goto or adding exception handling to the first milestone.

Valid C aliasing is not a reason to preserve weak view contracts. The
follow-up [ownership-only probe](borrow-probes/alias-owned.click) verifies the
same C and postcondition without a conflicting view, and the
[field-split probe](borrow-probes/field-split.click) preserves a caller's field
invariant using a view of the unchanged field. These support a contract
migration, not a claim that the new borrow rules have been implemented.
Do not call a mutable reborrow a duplicable owner. Only the explicitly scoped
basic C++ issue adds a second-language requirement to P1.

## Rust's first support slice, after C++

The next language milestone should be basic **safe, monomorphic Rust with
scoped references**: small functions over `i32`, `u32`, `bool`, and plain
struct fields; local initialization, branches, direct calls, shared/exclusive
reference parameters, and local reborrowing. Return scalars or supported
plain values initially. Use a pinned toolchain and target, no external crate
dependencies, and an explicit panic policy. Overflow/bounds checks must be
proved unreachable or modeled; accepting safe Rust is not itself proof of a
functional postcondition or absence of panics.

The defining positive should lend a mutable field to a helper, use a shorter
shared or mutable reborrow, end it, and then reuse the parent. Prove the final
value and preservation of another field. Reject conflicting accesses and a
false postcondition. Pair source tests with adversarial checked-transition
tests so compiler rejection alone is not mistaken for kernel validation.

Collect source spans, type validity, moves/initialization, and relevant loan
information at the selected MIR phases. Reconcile this with the lowered
execution operations. State precisely which compiler analyses are trusted
and which obligations Click checks; do not simply remove borrow operations
and execute the remainder as C.

Defer returned references, general generics/traits, enums with complex validity,
trait objects, closures, async, unsafe code, interior-mutability libraries,
standard-library verification, and threading to later slices. Returned field
borrows remain an early design model requirement in `fix-views`; actual Rust
surface support follows when contracts can bind the escaping lifetime and
connect the final borrowed value to the recovered owner. No separate Rust
implementation issue is filed until that milestone is requested.

## Later coverage and investigation gates

Broader language support should proceed through semantic examples rather than
ever wider syntax acceptance:

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

For C++, follow normal cleanup with object initialization/validity and storage
reuse, class copy/move and temporaries, then exceptions and partial
construction. Template instantiation can use compiler-resolved definitions,
but template syntax support is not a library proof. Virtual dispatch,
inheritance/subobject identity, standard-library contracts, and concurrent
objects each need explicit semantic coverage before taking on a large project.

For Rust, follow scoped borrowing with returned references, initialization
wrappers such as `MaybeUninit`, drops after moves and partially initialized
values, and checked sharing protocols for `Cell`, `RefCell`, and `Mutex`.
Treat `Pin`, unsafe raw-pointer aliasing, reference provenance, enum validity,
and atomics as dedicated semantic investigations. Destructors are not a
universal liveness guarantee: safe code can intentionally forget values, so
recovery must follow checked authority and lifetime rules.
[Rust `forget`](https://doc.rust-lang.org/std/mem/fn.forget.html)

Concurrent C is an independent check on the common resource model, not a
feature that becomes solved by implementing Rust. Begin with shared readers,
disjoint writers, and lock protocols; later test release/acquire publication
against an explicit memory model. Linux RCU, inline assembly, volatile/device
memory, FFI, build configurations, and platform contracts are further boundaries
on any claim to verify whole systems software. Language parsing alone does not
cover them. The [concurrency issue](../issues/concurrency-and-atomics.md) and
[compiler/ABI issue](../issues/multiple-compilers.md) own those implementation
areas when scheduled.

Keep unsupported behavior explicit and preserve the original program source.
Each new slice needs a real source witness, a false-claim/invalid-operation
counterexample, a precise trust and target boundary, ordinary proof-tool
agreement, and evidence that checking scales with the selected program and
certificate. Preserve these criteria when the current P1 issues close.
