# Checked input facts retain their pre-call read state

The call accepts the disjunction from the known input value. The input
proposition remains true of that old read, and cannot establish the same
proposition after the callee writes zero.

```c filename=call_checked_input_facts_keep_prestate.c
void clear(int32* p) { *p = 0; }
void caller(int32* p) { clear(p); }
```
```click
verifying "call_checked_input_facts_keep_prestate.c";
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
fail: checked outcome `close`
```
