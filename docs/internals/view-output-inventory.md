# Stable-view output inventory

This is the durable V13 audit of the explicit `views` and view-producing
surfaces in the current C corpus. It records what each surface means under the
stable-view rules in `issues/fix-views.md`; it is not an inventory of a new
escaping-loan feature.

## Snapshot and extraction

The snapshot below was generated on 2026-09-12 from the integrated V17
contract migrations at commit `41437441`. The extraction deliberately reads
only Click code blocks in `mdtests/*.md`, and whole `*.click` files in
`examples/` and `design/borrow-probes/`. It counts non-comment lines whose
first token is `views`, so prose mentions and C source embedded in a different
block cannot silently enter the inventory.

```text
files containing a view declaration: 198
view declarations:                  337
  mdtests:                          178 files
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
same semantic role. Each declaration is assigned one of the four output
classes below by the lowering/checking path that consumes it.

## Classification and outcome

| Inventory class | Extraction/count rule | Outcome under stable views |
| --- | --- | --- |
| Existing outer dependency | The 337 explicit `views` declarations above, when used to read memory already owned by the caller or an enclosing resource | Preserve the outer dependency. A view grants read access for the checked scope; it does not create an independent owner or lifetime. The V13 ordinary-reader, nested-reader, and partial-borrow examples exercise this class. |
| Returned input access | Function/resource return planning that carries a view derived from an input occurrence. The relevant implementation paths are `function_resource_summary`, `evaluate_contract_return_resources`, `candidate_output_views`, `returned_views`, and `recover_candidate_stable_view_resources` in `src/kernel/functions.rs` | Preserve only the checked input dependency and its occurrence identity. A returned view cannot mint a fresh authority or extend the input lifetime. This is the class for returned input access, rather than an escaping loan. |
| Immutable support | Resource-fact observation and composite expansion: `resource_clause_section_supply`, `selected_instance_arm_views`, `expand_composite_resource_fact`, and the selected-arm helpers in `src/kernel/loops.rs` | Use views as immutable support for the fact while its source occurrence remains live. The `stable_view_fact_workflow` mdtest covers the public validation/lowering path; dynamic loan capture remains the V12 follow-up dependency. |
| Unsupported escape | Any output form that would retain a stable view after its checked dependency ends. There is no supported `produces views` surface form. The raw returned-pointer case in `stable_view_returned_pointer` is deliberately classified here for a stable loan: the C pointer remains legal only because the caller retains independent ownership and performs the later write through that ownership. | Reject an escaping stable loan. Do not add implicit lifetime extension or an output resource that hides the missing dependency. |

The classification also covers legacy unbound `CResourceFact::View` values. A
current-state view fact may be statically recognized by V12, but it must not be
treated as stable merely because an old surface clause says `views`: the
dynamic loan binding must capture the actual source occurrence before the fact
can survive a transfer, fold, call, or output boundary. Until that dynamic
piece lands, `stable_view_fact_workflow` is a validation/lowering witness and
not evidence for an escaping view.

## Source-path audit

The audit has a concrete owner for each semantic class:

* `src/surface/parser.rs` and `src/surface/verification.rs` parse and
  summarize the existing dependency. They do not introduce a view-output
  lifetime.
* `src/surface/lowering/resource_lowering.rs` lowers a view requirement to a
  `CResourceFact::View`; its output is still tied to the enclosing occurrence.
* `src/kernel/functions.rs` validates returned resources and recovers candidate
  stable-view resources only when the checked input dependency is present.
* `src/kernel/functions.rs::resource_clause_section_supply`,
  `selected_instance_arm_views`, and
  `expand_composite_resource_fact` provide immutable composite/resource-fact
  support. They are not output authority.
* `src/kernel/loops.rs::with_selected_arm_views` and
  `with_guard_prefix_arm_views` add the same scoped support to loop proof
  states; they do not preserve it beyond the loop state.
* `src/kernel/loans.rs::LoanViewBinding` is the identity-bearing representation
  required for the dynamic V12 step. Any output path that lacks such a binding
  remains an unsupported stable-loan escape.

The V13 fixture set gives normal proof-workflow coverage for each relevant
shape: `stable_view_ordinary_reader`, `stable_view_nested_reader`,
`stable_view_partial_borrow`, `stable_view_fact_workflow`, and
`stable_view_returned_pointer`. The existing shared-reader fixtures remain in
place; the migration removes only overlapping sequential aliases and whole
composite-view/owned-field contracts that claimed more stable read access than
their implementation needed.

The candidate kernel transition is already covered by the focused
`candidate_stable_view_call_tests` in `src/kernel/functions.rs`. The surface
`ViewSemanticsMode::StableLoans` selector still needs one shared top-level
input-capability initialization before these corpus fixtures can run through
that selector: an independently verified function begins with an assumed view,
so it needs a checked nonrecoverable root authority tied to the exact resource
occurrence. The attempted surface route correctly fails closed at that
boundary; the V13 sidecar fixtures therefore remain legacy-route witnesses
until that common proof/certification state constructor is integrated. This is
the concrete V12 dynamic dependency, rather than a reason to weaken
`checked_loan_evidence_is_valid` or skip candidate evidence.

When V12 dynamic capture is integrated, rerun the extraction and this table's
fixtures. A changed count requires a classification entry or an explicit
unsupported-escape rejection; a newly accepted output must name its retained
input occurrence and prove that its lifetime is still live at every use. The
V17 contract migrations reduced the snapshot from 200 files/345 declarations
to 198 files/337 declarations by removing redundant view requirements; they
did not change the four semantic classes above.
