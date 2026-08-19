# WIP fallout log

## nested_field_segments_keep_the_terminal_field_offset (first audit)

The write's `execute` now needs the defining equation (`v == load`) as a
theorem premise and fails: "condition-certificate premise search did not
derive int32 equality is true from 0 ambient condition facts: []". The
defining fact rides the CExpressionPath fact stream, but the
condition-certificate premise search consults an ambient condition-fact
channel that is empty at that point. Fix direction: route the defining
fact into the channel the premise search consults (find where
"condition-certificate premise search" collects its ambient facts and
whether path facts should feed it), or emit the defining fact earlier so
assumptions_with_path_context carries it into step certification. This
symptom likely underlies several of the 14 — verify against the next
tests before fixing one-off.

## Layer 1 fixed: the defining fact is certified, not derivable

`ExecutionPureFact::certified` (not `::new`) marks the defining equation
as kernel-certified by construction — the fresh variable is the kernel's
own name for the load. The "assumption-derived theorem premise without a
replayable derivation" class disappears across the affected tests.

## Layer 2 surfaced: kernel variables need surface spellings

Next failure class: "kernel fact has no recorded or structurally
synthesized Click spelling: ConditionIs(PointerOffsetEqual(Int32Scaled {
value: Variable(..)" — surface synthesis (frame certificate lowering)
must spell facts mentioning the minted variable. The fix direction:
when synthesizing a spelling for a kernel variable, resolve it through
its defining fact to the load's recorded surface spelling
(surface_synthesis-side), or record a surface alias at mint time via
the replay's surface record (lang-side plumbing at the drain boundary).
Re-diagnose the outcome-match class (Variable(2) vs certification
spelling) after this layer: the certified flag may have changed it too.
