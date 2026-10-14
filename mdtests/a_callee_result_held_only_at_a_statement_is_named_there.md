# A callee's result no live local holds is named where a local held it

`caller` stores `value()`'s result in `r` and returns `r + 1`. At the outcome
no local is live, so `r`'s value has no current name; it is exactly what `r`
held at the end of the statement that assigned it, which an `ensures` can
cite as `at(statement(1).exit, r)`. The refusal names it that way, not as an
unnamed placeholder.

```c filename=a_callee_result_held_only_at_a_statement_is_named_there.c
int32 value(void) { return -56; }
int32 caller(void) { int32 r = value(); return r + 1; }
```

```click
verifying "a_callee_result_held_only_at_a_statement_is_named_there.c";
int32 value() { ensures result == -56 by auto; }
int32 caller() { ensures result == 200 by auto; }
```

```expect
fail: left side evaluated to at(statement(1).exit, r) + 1, right side evaluated to 200
```
