# Composite memory ranges must preserve unsigned element types

## Invariant

Unfolding a resource containing a `uint32*` range must materialize uint32
cells, not int32 cells. Equivalent direct memory and composite resource
contracts must permit the same C reads. This blocks the following startup
resource-packaging regression; ordinary ownership of the static array works.

## Intended regression

The unchanged C and sidecar below should pass. Currently `read_pair.contract`
fails while unfolding with a runtime type mismatch. Preserve this C source.

```c filename=main.c
unsigned int state[2] = {7, 9};
unsigned int read_pair(unsigned int *p) { return p[0] + p[1]; }
int main(void) { return read_pair(state); }
```

```click
resource pair(p: uint32*) { owns p[0..2]; }
verifying "main.c";
unsigned int read_pair(unsigned int *p) {
    requires loadable(p[0..2]);
    consumes pair(p);
    produces pair(p);
    ensures result == old(p[0]) + old(p[1]);
} by { unfold(pair(p)); execute(); fold(pair(p)); simp(); }
int main() {
    ensures result == 16;
} by { fold(pair(state)); execute(); simp(); }
```

## Acceptance criteria

- Preserve the declared pointee type when instantiating composite ranges,
  including substituted pointer values, without weakening load type checks.
- Make this fixture verify, expand, and reverify; cover unsigned 32/64-bit
  ranges and a negative mismatched-type case.
- Preserve the existing pointer-word origin representation and pass
  `scripts/check.sh`.
