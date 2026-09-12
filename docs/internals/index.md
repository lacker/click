# Internals

Internals describe the current Click implementation for contributors. They are
not additional user syntax. Where an internal Rust name and a Surface Click
name differ, user-facing documentation uses the Surface Click name.

## Architecture and trust

- [System architecture](architecture.md)
- [Proof objects](proof-objects.md)
- [Kernel implementation](kernel.md)
- [Separation logic](separation-logic.md)
- [Memory derivation DAG](memory-dag.md)
- [Mathematical integers](mathematical-integers.md)

## Engineering constraints

- [Verification efficiency](verification-efficiency.md)
- [Testing Click](testing.md)
- [Feature playbook](feature-playbook.md)
- [Contributing](contributing.md)
- [Maintainer quickstart](maintainer-quickstart.md)

## Project direction

- [Rbtree launch roadmap](roadmap.md)

The roadmap is to complete P1, verify rbtree, and launch publicly with rbtree
as the key demo. It describes intended work, not accepted syntax or a stability
promise. The technical reference remains authoritative for current behavior.
