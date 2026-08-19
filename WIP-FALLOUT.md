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
