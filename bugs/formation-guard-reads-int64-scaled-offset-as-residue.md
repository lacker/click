# The byte-offset helper folds an Int64Scaled offset into a 32-bit residue

P1. Index arithmetic wraps at 32 bits; pointer byte offsets are exact i64.
A helper that turns the exact delta into a residue violates the refusal the
codebase's own helpers make.

## What was found

`byte_offset_from_pointer_offset` (`src/kernel/reasoning/path_facts.rs:808`)
has an `Int64Scaled{value, byte_width}` arm at lines 815-820 that folds the
64-bit scaled displacement into a *modular 32-bit* `value * width` term.
The codebase's own comment one screen up states the honest refusal ("an
`Int64Scaled` one is not a residue of the delta", `path_facts.rs:449-463`,
`exact_element_delta_from_offset` refuses the same arm at
`path_facts.rs:698-702`) — the byte-width helper is the same question with
the modular shortcut installed instead.

Consumers reading the residue as a number: the in-bounds arm of
`pointer_block_bounds` at `src/kernel/eval/operators.rs:1847-1851`
(byte width == 1) compares the folded term against the block size, and
`pointer_byte_offset_from_base` (`path_facts.rs:738-795`) feeds the same
residue into membership questions. An access whose true byte displacement
exceeds the block by a whole `2^32` window contributes a small positive
residue and the guard reads "in bounds".

## Minimal C

```c
char a[8];
void probe(unsigned long long k) {
    if (k == 0x100000003ULL) {   /* established by 64-bit facts */
        a[k] = 1;                /* true offset 4 GiB + 3: UB */
    }
}
```

Route: with `k` pinned to `0x100000003` by exact-sixty-four-bit facts, the
formation-length guard term folds to `Constant(3)`, `3 <= 8` decides true,
and no `PointerArithmetic` path survives although the true displacement is
past the block.

## Intended regression

Mirror the machine verification in the file: evaluate the statement with
the 64-bit equality in the fact context and assert a
`CUndefinedBehavior::PointerArithmetic` path exists (or the guard refuses),
contra the wrapped guard's in-bounds answer. The fix at the helper is the
same shape as `exact_element_delta_from_offset`'s refusal: `None` for the
`Int64Scaled` arm unless the 64-bit facts pin the displacement inside an
exact, in-range window.

## Acceptance

- [ ] `byte_offset_from_pointer_offset` refuses (or window-bounds) the
      `Int64Scaled` arm; the pinned-by-64-bits out-of-range access
      regression produces the UB path.
- [ ] `scripts/check.sh` green.
