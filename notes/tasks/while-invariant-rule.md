# while-invariant rule: single-fork preservation check

Status: open
Claimed:

Scope (design-review honorable mention): the while-invariant rule
checks preservation in only one condition-fork context and against
pre-body state (old api.rs:2633; re-locate). Currently exercised only
by tests but exported. Either fix the rule to check both fork contexts
against the right state, or fence it (unexport / doc-comment the
limitation) so nothing user-facing can rely on it.

Done when: the rule is sound or unexported, with a kernel test pinning
whichever behavior is chosen; gates green.
