# A bare `transport` refusal names the leaf its frame could not carry

`dst[3] = 0` overwrites one of the cells `memset` set to `7`, so the claim
that all four still hold `7` is false and the bare `transport` is refused.
A bare `transport` cites only its source, and its refusal is the one the
same transport gets with its source listed in `using`: the
quantified frame's refusal, naming the typed validity fact it could not carry, its two states, and the
store to `dst[3]` among the effects between them. It ends by calling the
refusal a search miss and naming the `using` form that writes the evidence.

```c filename=fill.c
#include <string.h>

void fill(unsigned char *dst) { memset(dst, 7, 4); dst[3] = 0; }
```

```click
verifying "fill.c";

void fill(uint8* dst) {
    owns dst[0..4];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    step();
    mark filled;
    step();
    transport(at(filled, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })),
              (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }));
}
```

```expect
fail: quantified frame: a leaf was not carried: a read in it was not shown unchanged between its two states by the steps between them and this context's facts
  leaf it had: defined(at(statement(1).entry, dst[k]))
  leaf it wanted: defined(dst[k])
  this is the refusal with the source as the only premise, which is all a bare `transport` cites
  this is a search miss, not a refusal; if the target holds, list the facts that carry the source in `transport(P, Q) using { ... }`, stating any that is not available with `have` first
```
