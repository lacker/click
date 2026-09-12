# Preserve ordinary operand reads around expression calls

P1: call lowering chooses an observable evaluation order that lets a false
contract verify. Reproduced at `3ad0d2e1`.

## Violated invariant

Lowering must preserve the observable evaluations permitted by the supported
C semantics, or reject an unsupported interaction explicitly. Hoisting a
call must not silently move a read of memory that the call can modify.

`lower_expression_pair` in `src/languages/c/syntax.rs` recursively obtains
prefix statements for binary operands, rejects the case where both operands
have non-assertion prefixes, and otherwise emits the prefixes before the
remaining binary expression. An ordinary variable or memory read produces
no such prefix, so a call that changes its value is always moved before it.
The analogous argument-lowering loop deserves coverage for the same risk.

## Small reproduction

`order.c`:

```c
static inline int set(int *p) { *p = 2; return 0; }
int order(void) { int x = 1; return x + set(&x); }
```

`order.click`:

```click
verifying "order.c";
int32 order() {
    ensures result == 2;
}
```

`click verify order.click` exits 0. The frontend executes `set` before
reading the other operand, so it only considers result 2.

The original C permits reading `x` before executing `set`, producing 1.
This is different from two conflicting unsequenced modifications: C11
specifies that the called function's execution is indeterminately sequenced
relative to evaluations in the caller that are not otherwise ordered with
it. See [WG14 N1570, section 6.5.2.2 paragraph 10](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf#page=100).

The review also compiled the original source with:

```sh
clang -target x86_64-linux-gnu -funsigned-char -std=c11 -O2 \
    -S order.c -o order.s
```

The resulting `order` function returns constant 1 (`movl $1, %eax; retq`).
The false proof therefore disagrees with an ordinary compiler execution on
Click's modeled target as well as omitting a permitted C evaluation.

This is independent of `short-circuit-operand-calls.md`: the reproduction
uses an ordinary addition with a call and a value-dependent read.

## Acceptance criteria

- Reject the false result-2 proof for the unchanged C function.
- Model the relevant permitted orders, or promptly reject a call/read
  interaction whose sequencing is not supported. Keep unaffected expression
  calls working.
- Cover dependent reads on either operand side, pointer loads as well as
  scalar variables, and analogous function-argument combinations.
- Where the program is supported, a result-in-{1,2} contract must reflect
  every permitted execution, with checked certificates for each path.
- Do not insert proof-only locals or change the C expression to repair its
  verification. `scripts/check.sh` passes.
