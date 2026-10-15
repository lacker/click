# Split descriptor return-resource checking repeats expensive work

Soundness: incomplete. A correct proof verifies, but a simple post-execution
assumption repeats expensive resource and memory reasoning. This demonstrates
checker slowness, not false acceptance.

The recovery archive at `6103c9f05` verifies the original split-field string
append [reproduction](split-descriptor-fold-exhausts-simple-budget/repro.md)
in fresh, expanded, rewritten and retained modes. After the byte-gap repair,
its completed profile still identifies the first final `assumption` at line 85
as 185,461 deterministic work units (902ms in this run). Its seven final
assumptions total 2.67s; the fold itself is now 164ms. The complete diagnostic
profile verifies successfully in 10.30s. Timings are observations, not portable
performance limits.

```sh
click verify bugs/split-descriptor-fold-exhausts-simple-budget/repro.md
click profile --top 8 bugs/split-descriptor-fold-exhausts-simple-budget/repro.md
```

The profile attributes 141,663 units to contract resource outcome
reconstruction and 87,446 to one return-resource evaluation. Those operations
nest and must not be added. The implicit returned resource was explicitly
folded before the assumption. Source inspection additionally finds that
`function_return_resources_definitionally_established` expands all held
composites before evaluating the returned clauses. This is a candidate source
of unrelated work; it is not yet a measured scaling attribution.

Acceptance criteria:

- Establish the selected return-resource path and reduce the repeated work;
  preserve unchanged C, split-field ownership, contracts and existing budgets.
- Check the selected returned units and necessary evidence using indexed work,
  rather than expanding unrelated held composites.
- Measure deterministic work across several unrelated-context sizes and selected
  output sizes. Keep joint resource consumption and complete access widths.
- Preserve fresh, expanded, rewritten and retained checks, and rejection of
  wrong values, missing ownership and duplicate exclusive returns.
- Remove private probes and update this report when the repair lands.
