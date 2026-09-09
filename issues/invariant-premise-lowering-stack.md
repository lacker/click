# Bound recursive premise lowering on the ordinary test stack

## Violated invariant

A normal proof attempt must verify or return a bounded local proof failure.
It must not overflow the ordinary Rust test-thread stack while lowering a
candidate premise. This blocks the explicit loop-closure migration.

## Reproduction

At master `13b167e8`, the unchanged
`mdtests/bubble_sort3_two_pass_sorted.md` verifies, and its grouped claim
expands. The following diagnostic then adds relevant entry-index and cell
facts, explicit swap transport, and explicit invariant bodies. Verification
of that modified proof aborts with a stack overflow; do not expand it.

In an isolated task worktree, temporarily add this test to
`src/surface/tests/loop_tests.rs` and run it with the ordinary bounded
`cargo nextest run --lib investigate_original_sort_explicit_transport`.
Do not retain a crashing test as part of the green gate.

```rust
#[test]
fn investigate_original_sort_explicit_transport() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/bubble_sort3_two_pass_sorted.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture.c_sources.iter().map(|(name, source)| (name.as_str(), source.as_str())).collect::<Vec<_>>();
    let click = fixture.click_source.as_deref().unwrap();
    verify_c0_sources(click, &sources).unwrap();
    let mut expanded = expand_c0_claim_source(click, &sources, "bubble_sort3_two_pass", CProofClaim::Grouped).unwrap();
    let preserve = expanded.rfind("preserve by {").unwrap();
    let branch = preserve + expanded[preserve..].find("if ").unwrap();
    expanded.insert_str(branch, r#"
        unfold(all_le_range);
        have j == 0 by {
            apply(int32_lt_successor_implies_le(j, 0)) using { j < 1; }
            apply(int32_le_and_not_lt_implies_eq(j, 0)) using { j <= 0; j >= 0; }
            assumption();
        }
        have p[0] <= p[2] by {
            instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0) using {}
            assumption();
        }
        have p[1] <= p[2] by {
            instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1) using {}
            assumption();
        }
        mark before_swap;
    "#);
    let swap_close = preserve + expanded[preserve..].find("close_invariants();").unwrap();
    expanded.insert_str(swap_close, r#"
        transport(at(before_swap, p[1] <= p[2]), p[0] <= p[2]) using {
            at(before_swap, p[1] <= p[2]); at(before_swap, j) == 0;
        }
        transport(at(before_swap, p[0] <= p[2]), p[1] <= p[2]) using {
            at(before_swap, p[0] <= p[2]); at(before_swap, j) == 0;
        }
    "#);
    let explicit = expanded.replace("close_invariants();", "close_invariants by { simp(); }");
    verify_c0_sources(&explicit, &sources).unwrap();
}
```

The C, contracts, and loop invariants are unchanged. An earlier variant
without the newly inserted `unfold(all_le_range)` also overflowed; adding
the unfold did not fix the tooling problem.

## Debugger evidence (2026-09-08, ARM64 debug build)

The debugger stopped at the stack probe on entry to
`AnnotationLowerer::lower_c_fragment_to_spec`. The callers were:

1. `lower_contract_expression_to_spec` / `lower_at_expression_to_spec`;
2. eight nested `click_proposition_to_spec_proposition` calls;
3. `lower_surface_proposition_direct`;
4. `available_surface_fact`, validating a candidate's typed premise form;
5. `selected_simp_derivation_with_surfaces`;
6. `try_upper_bound_split_closure` under an implication closure.

Static disassembly of the tested debug binary measured these stack
allocations, including the 32-byte register save:

- `click_proposition_to_spec_proposition`: 68,704 bytes per call;
- `lower_contract_expression_to_spec`: 26,752 bytes per call;
- `lower_c_fragment_to_spec`: 15,312 bytes per call.

Thus modest proposition nesting consumes over half a megabyte before
counting the surrounding smart-planner frames. This establishes large
recursive temporary frames, not an unboundedly growing proof object.
The full runtime cost is not yet diagnosed; do not promise that frame
reduction alone completes the proof.

The debugger-owned process was explicitly killed after the backtrace.
Ordinary crashed test processes were confirmed absent before subsequent runs.
No stack limit or tactic budget was increased.

## Intended fix and regression

Outline large nonrecursive match arms or otherwise move large temporaries
off recursive dispatch frames, preserving semantics and search limits.
Inspect both proposition and expression lowering, not only the final
function where the guard page was hit. Avoid changing global stack sizes.

Add deterministic multi-size tests for nested propositions with snapshot
expressions on an ordinary or explicitly smaller test stack. Add the
unchanged sorting diagnostic as a regression requiring either a verified
proof or a prompt, bounded planning miss. Only expand a successful proof.

## Acceptance criteria

- The reproduced proof never aborts or exceeds its existing bounds.
- Recursive lowering has proportional work and modest per-level stack use.
- Wrong or missing premises still reject; no new proof authority is added.
- The focused tests and `scripts/check.sh` pass.
- Delete this file and its index line when the fix and coverage land.
