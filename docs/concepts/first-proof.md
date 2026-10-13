# Your first proof

This walkthrough writes a contract for a small C function, verifies it with
`click verify`, and shows what a failing proof reports.

Start with an ordinary C function that cannot fail, in `zero.c`:

```c filename=zero.c
int zero(void) {
    return 0;
}
```

The claim about it goes in a Click sidecar, `zero.click`, next to the C:

```click filename=zero.click
verifying "zero.c";

int32 zero() {
    ensures result == 0 by auto;
}
```

Run Click on the sidecar:

```console
$ click verify zero.click
1 selected proof verified
```

The claim is small, but it contains the whole Click shape:

- `verifying "zero.c";` names the C source. The C itself is not changed.
- `int32 zero()` identifies the C function being specified. Click spells C
  types by their width, so C's `int`, `signed int` and `int32_t` are all
  `int32` (see [Supported types](../reference/language/c.md#supported-types)).
- `ensures result == 0` states the fact to prove.
- `by auto` asks Click's default automation to prove it.

Click symbolically executes the C function, sees that every path returns `0`,
and proves the postcondition. `click verify` exits with status 0 when every
claim is proved and 1 otherwise.

## A proof that needs a requirement

Now consider `increment.c`:

```c filename=increment.c
int increment(int x) {
    return x + 1;
}
```

The natural postcondition is:

```click filename=increment.click
verifying "increment.c";

int32 increment(int32 x) {
    ensures result == x + 1 by auto;
}
```

Click refuses it:

```console
$ click verify increment.click
proof error:
  `increment.ensures_0` tactic 0
  `execute()` produced undefined behavior
  signed overflow
  C statement at increment.c:2:5
  `return x + 1;`

tactic@4:
  auto;

To get a trace:
  click verify --trace-proof increment increment.click
```

In C, signed overflow is undefined behavior, and `x + 1` overflows when `x` is
the largest `int`. Click proves the absence of undefined behavior along with
every claim, so the call is safe only when `x + 1` fits. The contract needs a
requirement:

```click filename=increment.click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures result == x + 1 by auto;
}
```

```console
$ click verify increment.click
1 selected proof verified
```

This is an important Click habit: requirements are not just mathematical
assumptions. They also rule out bad C executions, and every caller must
establish them.

## What failure means

When a proof fails, it usually means one of three things:

- the C code does not satisfy the contract,
- the contract is missing a required precondition,
- or Click does not yet have enough proof support for the claim.

The proof failure is the start of the debugging process. Next, read
[Contracts](contracts.md) and [Propositions](propositions.md) to learn the two
languages used in that process. Once ordinary contract debugging is not enough, use the
[proof-failure triage guide](proof-failure-triage.md) to distinguish
proof-authoring work from unsupported semantics, missing functionality,
correctness bugs, and tooling failures.

To verify a function in an existing project, with its include paths, `-D`
settings, and libc calls, continue with
[Verify a function in your own project](own-project.md).
