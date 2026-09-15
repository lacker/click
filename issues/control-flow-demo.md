# P1: Control-flow demo with cleanup jumps and exception unwinding

## Objective and violated invariant

Requested on 2026-09-15 as a before-launch architecture milestone. Verify two
small original programs: a C cleanup jump and a C++ exception crossing a call
boundary. The shared execution model must represent transfers, cleanup, and
normal/exceptional outcomes without assuming every call returns normally or
that execution always advances through a lexical statement tree.

Every reachable outcome must carry its actual state and resource obligations.
Skipped statements cannot contribute effects; a resource acquired on only one
path cannot be freed on another; unwinding cannot recover loans or resources
merely because a lexical scope ended. Rbtree remains the main launch demo.

## Dependencies and ownership of work

1. The P1 forward-cleanup slice of [goto.md](goto.md) supplies checked C labels,
   jumps, target resumption, and joins. It is required for this demo. General
   backward jumps and irreducible control flow remain P2.
2. [basic-cpp-support.md](basic-cpp-support.md) supplies the typed C++ frontend,
   object lifetimes, and normal scope cleanup. It remains a non-throwing slice
   and can complete before this issue.
3. This issue adds the narrow cross-call exception model and proves both
   end-to-end cleanup programs. The same edge/state infrastructure should
   serve C jumps and C++ cleanup, with language-specific legality rules.

The C++ exception probe does not semantically depend on C goto syntax; both
feed the shared edge design. Do not introduce a dependency cycle by requiring
the first C++ slice or the goto primitive to finish this whole demo first.

## Program 1: C cleanup after partial acquisition

Select a small C function that acquires two resources in sequence and uses
forward `goto` cleanup labels on failure. The labels may form a cleanup chain.
Prove that first-acquisition failure releases nothing, second-acquisition
failure releases only the first resource, and success releases both exactly
once while returning the specified result. Resource release is ordinary C
executed at the labels, not an automatic destructor synthesized for C.

Use symbolic success/failure outcomes under checked allocation or resource
contracts. Keep the C fixed before writing sidecars; do not replace jumps with
flags, duplicate cleanup bodies, or move declarations to satisfy the verifier.
Choose the initial source within the documented forward-jump slice and preserve
the original whenever a genuine tooling gap is found.

Reject missing release obligations, double release, releasing an unacquired
resource, executing a skipped mutation, and merging facts or ownership from
mutually exclusive acquisition paths. Include unknown/duplicate label and
unsupported-target diagnostics from the goto issue.

## Program 2: C++ exception across a helper call

Use two non-throwing scoped guards with distinguishable destructor effects.
After they have been constructed, call a helper that either returns normally
or throws a simple scalar exception. Catch the matching exception outside the
guard scopes. Prove reverse destructor order and exact final resource/state
effects on both normal and exceptional paths, together with the appropriate
return or catch result. The helper's body and both outcomes must be verified
modularly; inlining one known throw site is insufficient.

Add a companion path where the helper throws before the second guard is
constructed. Only the first guard is destroyed on that path. Use this to pin
conditional lifetime tracking without requiring constructors that themselves
throw. Reject a wrong cleanup order, omitted/duplicated destructor effects,
use of an unconstructed guard, and a normal postcondition imported into the
exceptional outcome. An exceptional path must not vanish just because the
selected contract lacks an exceptional guarantee.

Select and document one exception-enabled C++20 compiler/import profile;
preserve its distinction from the first C++ profile with exceptions disabled.
Pin the throw/catch type, handler selection, exception payload transport,
unwinding effects, and runtime assumptions. A scalar exception with a matching
handler and non-throwing guards is sufficient. Compiler lowering/runtime
support is a stated trust boundary, not proof of an exception ABI implementation.

## Required architecture and workflow

- Give function contracts checked normal and exceptional outcomes, or an
  equivalent explicit outcome representation. Each retains its own facts,
  memory effects, resources, and supported lifetime/loan transitions.
- Make edges and cleanups certificate-visible with original source locations.
  Match handlers by the supported language rules; cannot-tell is not evidence
  that a call returns or that a particular handler catches its exception.
- Keep C jump legality distinct from C++ initialization and cleanup legality.
  Preserve return-value capture before normal cleanup and exception transport
  across callee/caller boundaries.
- Reuse the ordinary bounded engine and simple rules. Verify first; require
  expand/reverification, profile, and audit to agree on the original source.
  Unsupported transfers get bounded local diagnostics.
- Follow the [efficiency contract](../docs/internals/verification-efficiency.md).
  Deterministic regressions at four or more sizes must cover edge/cleanup
  count and fixed transfers amid unrelated scopes, functions, and facts.
  Check only the selected edge, required cleanup, and produced delta; do not
  rescan complete source tails or every historical state per transfer.

## Acceptance criteria and deferred scope

- Both original programs, their modular proofs, all outcome/cleanup negatives,
  and reproducible commands are in the normal fixture gates.
- Forward goto primitives meet their own P1 criteria. The exceptional helper,
  caller, and destructor contracts are checked, and hostile certificates
  cannot omit an outcome or invent cleanup/resource recovery.
- A durable design record covers the edge/outcome model, supported exception
  profile, trust assumptions, and scaling evidence. `scripts/check.sh` passes;
  delete this issue and its list entry when all work lands.

General backward/irreducible jumps, `setjmp`/`longjmp`, exception inheritance,
rethrow, throwing constructors/destructors, termination during double
unwinding, Rust panic, and coroutines are deferred. Keep these distinctions
explicit so the first exception proof is not advertised as general C++
exception support. Follow `AGENTS.md` when verifier or proof tooling blocks work.
