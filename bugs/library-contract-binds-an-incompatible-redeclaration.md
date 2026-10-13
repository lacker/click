# A library contract binds to an incompatible redeclaration

Soundness: soundness-adjacent. Click verifies a call through a program's own
declaration of a standard-library function whose type is incompatible with
the library's, binding Click's contract for that name anyway. The reproduction
below passes a `const char *` to an `int` parameter, a constraint violation
that GCC 14 and Clang reject, so the accepted program does not build; no false
claim about a program that builds is known. A program that declares a library
function with a compatible but different type, then calls it, has undefined
behavior (C11 6.2.7p2, 6.5.2.2p9) that Click does not report.

Click's standard-library contracts bind by function name: a call to `strlen`
uses `extern uint64 strlen(const uint8* bytes)` from `stdlib/prelude.click`
whichever C declaration is in scope. This is intended, since a program may
declare `strlen` itself, and a compiler import may select a project header in
place of Click's `<string.h>`. The C declaration must still be compatible
with the library function. For a function without a library contract the
argument binding already refuses the mismatch (`could not bind arguments for
g`).

Reproduced on `importsys` (master `6266afe` plus compiler-import system
headers), direct mode:

```c filename=main.c
int strlen(int s);
unsigned long last_index(const char *s) {
    unsigned long n = strlen(s);
    return n;
}
```

```click
target "x86_64-linux-userspace";
verifying "main.c";

uint64 last_index(const char* s) {
    requires cstr_readable(s);
    ensures s[result] == '\0';
} by {
    execute();
    simp();
}
```

`click verify` prints `external assumptions: last_index -> strlen` and `1
selected proof verified`. `gcc-14 -std=c11 -fsyntax-only main.c` fails with
`passing argument 1 of 'strlen' makes integer from pointer without a cast`
and warns `conflicting types for built-in function 'strlen'`; Clang fails with
`incompatible pointer to integer conversion` and warns `incompatible
redeclaration of library function 'strlen'`. With `int strlen(const char *s);`
Click instead treats the result as `uint64` and asks for an `int32` narrowing
bound.

Intended regression: an mdtest with the C above whose `expect` block refuses
the declaration, plus one with `int strlen(const char *s);`.

Acceptance criteria:

- A declaration of a function that has a standard-library contract is
  refused, naming the function and both types, unless its type is compatible
  with the library's (for `strlen`, `size_t (const char *)`, with the
  documented plain-`char` byte view).
- Click's own `<string.h>` and `<stdlib.h>` declarations, and compatible
  program prototypes such as those in `mdtests/ext_memcpy_allocation_authority.md`,
  still bind.
- The rule holds in direct mode and in a compiler import.
