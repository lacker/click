# Resource proof steps must retain static bindings

## Invariant

Folding a resource around owned static storage must use the same lexical
bindings as an ordinary C expression. Several resource proof paths currently
discard the CState locals and pass only its memory to lowering, so `&state`
fails to resolve even when the exact state contains both the binding and
ownership. The issue is independent of program initialization.

## Intended regression

This unchanged program should pass. Currently folding in `main` reports
`could not lower resource cell argument 0` with zero evaluation paths.

```c filename=main.c
int state = 7;
int read_cell(int *p) { return *p; }
int main(void) { return read_cell(&state); }
```

```click
resource cell(p: int32*) { owns p[0..1]; }
verifying "main.c";
int read_cell(int *p) {
    consumes cell(p);
    produces cell(p);
    ensures result == old(p[0]);
} by { unfold(cell(p)); execute(); fold(cell(p)); simp(); }
int main() { ensures result == 7; }
by { fold(cell(&state)); execute(); simp(); }
```

## Acceptance criteria

- Use the exact existing state when lowering resource arguments in fold,
  unfold, observe, and their certificate-recording paths; preserve parameter
  shadowing and private translation-unit identities.
- Make the example verify, expand, and reverify without C changes.
- Reject folding unowned or aliased storage twice, and keep `scripts/check.sh`
  green. Do not change ownership algebra or infer extra permissions.
