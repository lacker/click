# A narrowing of a value the path holds as a constant is a bare `type mismatch`

Soundness: not soundness. The conversion is refused either way; only the
report is wrong. It names neither the narrowing bound that fails nor the
value that fails it.

A checked C narrowing conversion (to `int8`, `uint8`, `int16`, `uint16`, or
`int32` from a 64-bit source) owes the destination's range. When the facts
refute the bound, the report says so:
`mdtests/a_refuted_narrowing_initializer_names_its_range_and_value.md` prints
`missing prerequisite (uint8 narrowing lower bound): the facts refute
`x >= 0``. When the converted value is a constant in the evaluator's state
(here, a local initialized from a constant) the same conversion reports only
`type mismatch`, because `add_narrowing_bound_obligation` in
`src/kernel/eval/expression.rs` returns `None` for a bound the constant fails
on its own and the caller turns that into `CRuntimeError::TypeMismatch`.

An integer constant *expression* written at the conversion no longer reaches
this path: the C front end converts it modulo 2^N as GCC does
(`mdtests/an_out_of_range_integer_constant_converts_modulo_its_destination_width.md`).

Reproduced on `gccconv` (based on `46371bd`):

```c filename=a.c
int f(void) { int x = -56; unsigned char c = x; return c; }
```

```click
verifying "a.c";
int32 f() { ensures result == 200 by auto; }
```

```text
proof error:
  `f.ensures_0` tactic 0
  `execute()` could not verify C operation
  type mismatch
  C operation
  c = x
```

The same program with `int32 f(int32 x) { requires x == -56; ... }` reports
`uint8 narrowing lower bound: the facts refute x >= 0`.

Acceptance criteria:

- The refusal names the failing bound (`uint8 narrowing lower bound`) and the
  value, as the facts-refuted case does, for initializers, assignments,
  returns, and arguments.
- An mdtest pins the reproduction above with that expected text.

Whether such a conversion should be refused at all is a separate policy
question: GCC defines it (modulo 2^N), and the maintainer principle is that
Click accepts what GCC and Clang accept with the same meaning. Changing the
checked narrowing rule is a design decision, not this bug's fix.
