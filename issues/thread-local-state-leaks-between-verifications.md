# Thread-local state leaks between verifications on one thread

## Violated invariant

Verifying a project is a pure function of its sources and budgets. Running
two projects back to back on one thread must give each the same verdict it
gets alone.

It does not. On one thread, `verify_c0_sources` over `examples/borrowed-slice`
followed by `examples/linked-list` fails the second with

```
`list_roundtrip.contract` path 0, tactic 2: checked outcome `simp` search did
not retain a complete proof for `list_roundtrip.ensures_3`
```

while `linked-list` alone, or after `input-cursor` or `owned-string`, passes.
The sequence passes again with any one of `CLICK_DISABLE_DECIDE_MEMO`,
`CLICK_DISABLE_MEMORY_DAG`, or `CLICK_DISABLE_TACTIC_BUDGETS` set, so a
thread-local memo (the decide memo, or a DAG-walk memo keyed by arena ids
and derivation generation) answers a later project's query from an earlier
project's state and the changed answer pushes the smart search past its
budget. The fixture gates never see this because they verify each file in a
fresh thread.

Reproduced on 83986bbf, before the canonicalization chunk that found it.

## Reproduction

```rust
#[test]
fn verifications_on_one_thread_are_independent() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for (project, sidecar) in [
        ("borrowed-slice", "borrowed_slice.click"),
        ("linked-list", "linked_list.click"),
    ] {
        let path = manifest.join("examples").join(project).join(sidecar);
        let click_source = std::fs::read_to_string(&path).unwrap();
        let sources = crate::cli::read_verifying_sources(&path, &click_source).unwrap();
        verify_c0_sources(&click_source, &crate::cli::source_refs(&sources))
            .unwrap_or_else(|error| panic!("`{project}` failed: {error:?}"));
    }
}
```

Once this issue is fixed, land the regression above and delete this file.

## Acceptance criteria

- The reproduction above passes on one thread, and a regression with that
  shape (two example projects, one thread) is in the unit suite.
- The leaking state is identified and either keyed so a different project
  cannot hit it (content, not arena id or address), or cleared at
  verification entry with a documented reason.
