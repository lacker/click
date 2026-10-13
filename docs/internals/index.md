# Internals

Internals describe the current Click implementation for contributors. They are
not additional user syntax. Where an internal Rust name and a Surface Click
name differ, user-facing documentation uses the Surface Click name.

## Architecture and trust

- [System architecture](architecture.md)
- [The verification pipeline](../concepts/verification-pipeline.md)
- [Surface Click and Kernel Click](../concepts/surface-and-kernel.md)
- [Proof landscape](../concepts/proof-landscape.md)
- [Proof objects](proof-objects.md)
- [Kernel implementation](kernel.md)
- [Separation logic](separation-logic.md)
- [Stable views](stable-views.md)
- [Resource invariants and synchronization](resource-invariants.md)
- [Byte representation](byte-representation.md)
- [Memory derivation DAG](memory-dag.md)
- [The resource tracker](resource-tracker.md)
- [Fold read ranges](fold-read-ranges.md)
- [Mathematical integers](mathematical-integers.md)

## Engineering constraints

- [Verification efficiency](verification-efficiency.md)
- [Testing Click](testing.md)
- [Feature playbook](feature-playbook.md)
- [Contributing](contributing.md)
- [Maintainer quickstart](maintainer-quickstart.md)

## Project direction

- [C++ object model and shared memory semantics](https://github.com/clicklang/click/blob/master/design/cpp-object-model.md)
- [Rbtree launch roadmap](roadmap.md)
- [Supporting more languages: C++ first, Rust next](https://github.com/clicklang/click/blob/master/design/supporting-more-languages.md)

The roadmap is to complete P1, verify rbtree, and launch publicly with rbtree
as the key demo. It describes intended work, not accepted syntax or a stability
promise. The technical reference remains authoritative for current behavior.
