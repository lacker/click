# Linked initializers must resolve private names in their defining file

## Invariant

An external pointer initialized to private storage retains that object's
identity when linked into another translation unit. Re-evaluating its
initializer against the importing file's visible names is incorrect.

## Intended regression

Keep this C unchanged. Parsing currently rejects the initializer while
validating `main.c`, saying that only addresses of declared objects are
supported, although `value` is declared in the defining `data.c`.

```c filename=data.c
static int value = 11;
int *exposed = &value;
int zero;
```

```c filename=main.c
extern int *exposed;
extern int zero;
int read_cell(int *p) { return *p; }
int main(void) { return read_cell(exposed) + zero; }
```

```click
verifying "data.c";
verifying "main.c";
int read_cell(int *p) {
    requires loadable(p[0..1]);
    consumes p[0..1];
    produces p[0..1];
    ensures result == old(p[0]);
} by { execute(); simp(); }
int main() { ensures result == 11; }
by { execute(); simp(); }
```

## Acceptance criteria

- Resolve initializer references in the defining translation unit and retain
  the resulting storage identities across linking, without exposing private
  names to importing C code.
- Verify this program unchanged, with startup ownership of the private
  pointee. Include independent same-named private objects and data-only files.
- Reject unresolved initializers and conflicting definitions; run the full
  `scripts/check.sh` gate.
