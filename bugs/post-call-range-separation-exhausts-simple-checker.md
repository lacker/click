# Post-call range separation exhausts the simple checker

Priority: P2.

Soundness: incomplete. A simple separation check exhausts its deterministic
control budget on the bounded object-model recovery branch. This report does
not demonstrate a false accepted proof. Do not repair it by treating numeric
pointer equality as a full pointer identity.

## Reproduction

At recovery `7dde92bfe`, run the following Python script from the repository
root. It retains every original C file and contract. It only inserts explicit
resource-body transfers in the existing arena pipeline proof. The forward
transfer checks; after `arena_free(first)`, the reverse transfer stops in its
first separation proof. `assumption()` gives a bounded missing-fact refusal;
`simp()` exhausts 2,500,000 deterministic control units.

```python
from pathlib import Path
import subprocess

revision = "7dde92bfe"
source = subprocess.check_output(
    ["git", "show", f"{revision}:examples/arena/arena_cells.click"], text=True
)
destination = Path("target/arena-resource-transfer-budget")
destination.mkdir(parents=True, exist_ok=True)
for original in Path("examples/arena").glob("*.c"):
    content = subprocess.check_output(
        ["git", "show", f"{revision}:{original.as_posix()}"]
    )
    (destination / original.name).write_bytes(content)

def transfer(binding, old, new, indent, index, tactic):
    pad = " " * indent
    live, capacity = f"transfer_live_{index}", f"transfer_capacity_{index}"
    lines = [
        f"{pad}have {new} == {old} by simp;",
        f"{pad}let {{ live: {live}, capacity: {capacity} }} = unfold({binding});",
    ]
    occupied = f"memory({new}->occupied[0..{new}->capacity])"
    data = f"memory({new}->data[0..{new}->capacity])"
    header = f"memory(*{new})"
    for left, right in [(occupied, data), (header, data), (header, occupied)]:
        lines.extend([
            f"{pad}have separate({left}, {right}) by {{",
            f"{pad}    rewrite({new} == {old});",
            f"{pad}    {tactic}();",
            f"{pad}}}",
        ])
    lines.append(
        f"{pad}let {binding} = fold(arena_state({new}), "
        f"{{ live: {live}, capacity: {capacity} }});"
    )
    return "\n".join(lines) + "\n"

for needle, added in [
    ("        mark f1;", transfer("s0", "arena", "first->arena", 8, 0, "assumption")),
    ("        step(arena_destroy(arena), { st: g1 });",
     transfer("g1", "first->arena", "arena", 8, 1, "simp")),
]:
    assert source.count(needle) == 1
    source = source.replace(needle, added + needle, 1)
(destination / "arena_cells.click").write_text(source)
```

Run the resulting complete project under the normal limits:

```sh
CLICK_TIMINGS=1 cargo run --bin click -- verify   target/arena-resource-transfer-budget/arena_cells.click --trace-proof arena_pipeline
```

The failing goal is separation of the occupied and data ranges through `arena`.
After rewriting `arena == first->arena`, the trace retains the corresponding
separation through the returned state resource, but distinguishes the data
pointer reads used by the goal and the recorded premise. The current mismatch
is after a checked modular call, not an actual overlapping memory write.
Named-operation profiling identifies the open indexed goal equality rewrite
span (1,445,908 units), with 901,437 completed units in that route and
810,040 in selected premise reduction. Reduction of this exact comparison is
next.
The failed proof is not installed in the original example.

## Acceptance

- Reduce and fix the unbounded simple-checker work; retain the original-source
  complete reproduction as the compatibility witness.
- Establish the exact read/frame comparison or give a bounded refusal with its
  missing premise. Do not increase proof or timing limits.
- Preserve rejection of actual overlapping writes, stale snapshots and native
  pointer designation inferred only from equal numeric addresses.
- Recheck the original arena pipeline, all proof modes and the full normal
  example audit before declaring the compatibility work complete.
