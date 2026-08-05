# Reduce slow owned-string control proofs

## Problem

The default examples gate reports three completed CONTROL `have` proofs above
the two-second budget:

- two sites in `owned_string_push`, about 3.9s and 3.6s exclusive;
- one site in `owned_string_pop`, about 3.9s exclusive.

A control container should only organize nested work. Exclusive multi-second
cost means verifier work is happening outside properly attributed child tactics
or the container implementation itself is inefficient. The owned-string project
is quarantined while this and its separate smart-step issue are open.

## Work

Profile each site separately with start events enabled. Attribute the exclusive
time to parsing/lowering, branch-state copying, goal construction, or hidden
proof search. Any hidden search must become a classified child tactic with the
normal local deadline. Optimize deterministic container overhead rather than
expanding the `have` container.

## Acceptance criteria

- Each control site completes below the two-second control budget.
- Nested work is fully represented by SMART/SIMPLE timing events.
- Targeted and project profiles agree on exclusive time.
- Owned-string can leave quarantine once this and the smart-step issue pass.
