# Your First Proof

Start with a C0 function that cannot fail:

```c
int32 zero() {
    return 0;
}
```

The matching Click sidecar is:

```click
verifying "zero.c";

int32 zero() {
    ensures result == 0 by auto;
}
```

The claim is small, but it contains the whole Click shape:

- `verifying "zero.c";` names the C source.
- `int32 zero()` identifies the C function being specified.
- `ensures result == 0` states the fact to prove.
- `by auto` asks Click's default automation to prove it.

Click symbolically executes the C function, sees that every path returns `0`,
and proves the postcondition.

## A Proof With A Requirement

Now consider:

```c
int32 increment(int32 x) {
    return x + 1;
}
```

The natural postcondition is:

```click
ensures result == x + 1 by auto;
```

But in C, signed overflow is undefined behavior. The call is safe only when
`x + 1` fits in `int32`. The full contract needs a requirement:

```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures result == x + 1 by auto;
}
```

This is an important Click habit: requirements are not just mathematical
assumptions. They also rule out bad C executions.

## What Failure Means

When a proof fails, it usually means one of three things:

- the C code does not satisfy the contract,
- the contract is missing a required precondition,
- or Click does not yet have enough proof support for the claim.

The proof failure is the start of the debugging process. The next beginner
chapters explain the two languages you need to read that process: contracts and
propositions.
