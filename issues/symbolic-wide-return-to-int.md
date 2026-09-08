# Symbolic wide returns must support representable int conversion

## Invariant

An implicit conversion from a 64-bit integer to int must accept values proved
representable, including opaque helper results. Currently conversion requires
a syntactic constant; call equalities do not suffice. The startup resources
and wrapper postconditions below verify independently, but main is rejected
with `returned a value that does not match its declared type`.

## Intended regression

Keep this C unchanged. The desired whole-program result is 41.

```c filename=left.c
struct counter { unsigned long value; };
static struct counter state = {7};
unsigned long bump(struct counter *p) { p->value += 1; return p->value; }
unsigned long left(void) { return bump(&state); }
```

```c filename=right.c
struct counter { unsigned long value; };
unsigned long bump(struct counter *p);
static struct counter state = {40};
unsigned long right(void) { return bump(&state); }
```

```c filename=main.c
unsigned long left(void);
unsigned long right(void);
int main(void) { left(); return right(); }
```

```click
verifying "left.c";
verifying "right.c";
verifying "main.c";
unsigned long bump(struct counter *p) {
    requires loadable(p->value);
    consumes p->value; produces p->value;
    ensures p->value == old(p->value) + 1u64;
    ensures result == p->value;
    ensures result == old(p->value) + 1u64;
} by { execute(); simp(); }
unsigned long left() {
    consumes state.value; produces state.value;
    ensures state.value == old(state.value) + 1u64 by { execute(); simp(); }
    ensures result == state.value by { execute(); simp(); }
    ensures result == old(state.value) + 1u64 by { execute(); simp(); }
}
unsigned long right() {
    consumes state.value; produces state.value;
    ensures state.value == old(state.value) + 1u64 by { execute(); simp(); }
    ensures result == state.value by { execute(); simp(); }
    ensures result == old(state.value) + 1u64 by { execute(); simp(); }
}
int main() { ensures result == 41 by { execute(); simp(); } }
```

## Acceptance criteria

- Verify and expand/reverify the complete example without C changes.
- Check representability for signed and unsigned 64-to-int conversions; do
  not silently accept unproved bounds or choose out-of-range behavior.
- Cover boundary and out-of-range negative cases and run scripts/check.sh.
- Use locally checkable range/equality evidence, not global assumption scans.
