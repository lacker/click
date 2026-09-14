# Stable-view output inventory

This is the durable audit of the explicit `views` and view-producing surfaces
in the C corpus. It records what each surface means now that `views` is a
shared borrow.

## Snapshot and extraction

The snapshot below was regenerated on 2026-09-14 by the script that follows,
at the commit that made stable views the default. The extraction deliberately
reads only Click code blocks in `mdtests/*.md`, and whole `*.click` files in
`examples/` and `design/borrow-probes/`. It counts non-comment lines whose
first token is `views`, so prose mentions and C source embedded in a different
block cannot silently enter the inventory.

```text
files containing a view declaration: 201
view declarations:                  357
  mdtests:                          181 files
  examples:                          19 files
  design:                             1 file
```

The exact extraction method is kept here so a later language or contract
change can reproduce the audit and compare counts:

```python
from pathlib import Path
import re
from collections import Counter

files, declarations = [], []
for path in [*Path("mdtests").glob("*.md"),
             *Path("examples").rglob("*.click"),
             *Path("design").rglob("*.click")]:
    text = path.read_text()
    blocks = ([part.split("```", 1)[0]
               for part in text.split("```click")[1:]]
              if path.suffix == ".md" else [text])
    hits = []
    for block in blocks:
        hits.extend((line_number, line.strip())
                    for line_number, line in enumerate(block.splitlines(), 1)
                    if re.match(r"^\s*views\s+", line)
                    and not line.lstrip().startswith("//"))
    if hits:
        files.append(path)
        declarations.extend((path, *hit) for hit in hits)

print(len(files), len(declarations))
print(Counter("mdtests" if path.parts[0] == "mdtests" else path.parts[0]
              for path in files))
```

The counts are corpus bookkeeping, not a claim that every declaration has the
same semantic role. Each declaration is assigned one of the output classes
below by the lowering and checking path that consumes it.

## Classification and outcome

| Inventory class | Extraction/count rule | Outcome under stable views |
| --- | --- | --- |
| Existing outer dependency | The 357 explicit `views` declarations above, when used to read memory already owned by the caller or an enclosing resource | Lend the outer authority. A view grants read access for the borrow and suspends the lender's write, free, and lifetime authority until the return recovers it; it creates no independent owner or lifetime. The ordinary-reader, nested-reader, and partial-borrow fixtures exercise this class. |
| Returned input access | Function/resource return planning that carries a view derived from an input occurrence. The relevant implementation paths are `function_resource_summary`, `evaluate_contract_return_resources`, `candidate_output_views`, `returned_views`, and `recover_candidate_stable_view_resources` in `src/kernel/functions.rs` (the `candidate_` prefixes are leftover rollout spellings of the shipped path) | Preserve only the checked input dependency and its occurrence identity. A returned view cannot mint a fresh authority or extend the input lifetime. This is the class for returned input access, rather than an escaping loan. A carried view of read-only storage is accepted, because read-only blocks are intrinsic read authority with no ledger root. |
| Immutable support | Resource-fact observation and composite expansion: `resource_clause_section_supply`, `selected_instance_arm_views`, `expand_composite_resource_fact`, and the selected-arm helpers in `src/kernel/loops.rs` | Use views as support for the fact while its source occurrence remains live. An observation published from an owner the same context holds is authority derived from that owner, not a transferable borrow; one published through a borrow carries that loan's identity and is historical after the loan ends. |
| Escaping borrow inside a produced composite | An ensured owned composite whose definition body contains a `views` clause, backed by one of the call's own viewed inputs | Return the backing loan open, with the produced composite as its dependency. The caller keeps the escrow and the close and recovery rights and recovers its owner only when it unfolds or consumes the composite. Exactly one viewed input must be able to back each viewed piece; none or several is refused with a diagnostic naming the composite and the inputs. |
| Unsupported escape | Any other output form that would retain a stable view after its checked dependency ends. There is no supported `produces views` surface form. The raw returned-pointer case in `stable_view_returned_pointer` is deliberately classified here: the C pointer remains legal only because the caller retains independent ownership and performs the later write through that ownership. | Reject the escaping loan. Do not add implicit lifetime extension or an output resource that hides the missing dependency. |

The classification also covers unbound `CResourceFact::View` values. A
current-state view fact is not stable merely because a surface clause says
`views`: the loan binding must capture the actual source occurrence before the
fact can survive a transfer, fold, call, or output boundary.

## Source-path audit

The audit has a concrete owner for each semantic class:

* `src/surface/parser.rs` and `src/surface/verification.rs` parse and
  summarize the existing dependency. They do not introduce a view-output
  lifetime.
* `src/surface/lowering/resource_lowering.rs` lowers a view requirement to a
  `CResourceFact::View`; its output is still tied to the enclosing occurrence.
* `src/kernel/functions.rs` validates returned resources and recovers lent
  authority only when the checked input dependency is present.
* `src/kernel/functions.rs::resource_clause_section_supply`,
  `selected_instance_arm_views`, and
  `expand_composite_resource_fact` provide immutable composite/resource-fact
  support. They are not output authority.
* `src/kernel/loops.rs::with_selected_arm_views` and
  `with_guard_prefix_arm_views` add the same scoped support to loop proof
  states; they do not preserve it beyond the loop state.
* `src/kernel/loans.rs::LoanViewBinding` is the identity-bearing representation
  a borrowed fact carries, including the hold that an escaping borrow places on
  its backing loan. Any output path that lacks such a binding remains an
  unsupported escape.

The `stable_view_*` mdtests give normal proof-workflow coverage for each
relevant shape: `stable_view_ordinary_reader`, `stable_view_nested_reader`,
`stable_view_partial_borrow`, `stable_view_fact_workflow`, and
`stable_view_returned_pointer`. `examples/input-cursor` is the escaping-borrow
project. The kernel transitions are covered by
`stable_view_call_tests` in `src/kernel/functions.rs` and the loan
tests in `src/kernel/loans.rs`.

Rerun the extraction when contracts change. A changed count requires a
classification entry or an explicit unsupported-escape rejection; a newly
accepted output must name its retained input occurrence and prove that its
lifetime is still live at every use. The contract migrations that preceded the
cutover removed redundant and overlapping view requirements rather than adding
semantic classes; the classes above are the complete set.
