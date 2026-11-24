# A refusal names a fact the renderer cannot spell

After `clear(p)` writes zero, the caller holds the fact that its cell reads
zero at the call's exit. The diagnostic renderer has no recorded points, so
it can name that read only as `at(<state A>, p[0])`. The refusal prints the
fact's Surface form instead, `*p == 0`, because that form lowers back to the
same fact in the failed proof's context. The claim itself is false: the cell
is zero, not positive.

```c filename=a_refusal_names_a_fact_its_renderer_cannot_spell.c
void clear(int32* p) { *p = 0; }
void caller(int32* p) { clear(p); }
```
```click
verifying "a_refusal_names_a_fact_its_renderer_cannot_spell.c";
void clear(int32* p) {
    owns p[0..1];
    requires p[0] > 0 or p[0] == 1;
    ensures p[0] == 0;
} by { step_until(function.exit); close(); close(); }
void caller(int32* p) {
    owns p[0..1];
    requires p[0] == 1;
    ensures p[0] > 0 or p[0] == 1;
} by { step_until(function.exit); close(); close(); }
```
```expect
fail: pure facts: [*p == 0,
```
