# `memcpy` refuses a `const` source pointer

Soundness: incomplete. Click refuses a call to the modeled `memcpy` that is
valid C; nothing false is accepted.

Click's own user-space `<string.h>` declares
`void *memcpy(void *dest, const void *src, size_t n);`, and the C standard
lets any object pointer, `const`-qualified or not, convert to `const void *`.
A modeled library call must accept the arguments its declared prototype
accepts. Today a source argument of type `const char *` or
`const unsigned char *` is not bound to the standard-library contract, whose
source parameter is spelled `uint8 source[]` in `stdlib/prelude.click`, and
`execute()` refuses the call. The same source with a non-`const` pointer
verifies. `memcmp`'s two `const void *` parameters are spelled the same way and
should be checked with the fix.

Reproduced on master `8ab87b3`:

```c filename=copy4.c
#include <string.h>

void copy4(char *dst, const char *src)
{
	memcpy(dst, src, 4);
}
```

```click
verifying "copy4.c";

void copy4(char* dst, const char* src) {
    requires viewable(src[0..4]);
    owns dst[0..4];
    requires separate(memory(dst[0..4]), memory(src[0..4]));
} by {
    execute();
    simp();
}
```

```text
proof error:
  `copy4.contract` tactic 0
  `execute()` could not verify C operation
  function contract could not be applied
  could not bind arguments for memcpy
  ...
  C statement at copy4.c:5:2
  `memcpy(dst, src, 4);`
```

Removing `const` from `src` in both files makes it verify
(`external assumptions: copy4 -> memcpy`). The diagnostic also does not say
which argument failed to bind or why.

The original pattern is `examples/label-build-flags/label_copy.c`, whose
`label_copy` copies a `const char *src` with `memcpy` and is left unspecified
because of this refusal.

Intended regression: an mdtest with the C above whose `expect` block is
`pass`, plus a `memcmp` call over two `const unsigned char *` arguments.

Acceptance criteria:

- A `const`-qualified source pointer binds to `memcpy`'s contract, and
  `const`-qualified arguments bind to `memcmp`'s, keeping the representation-copy
  effect bound to the exact standard-library declaration.
- A `const` destination is still refused
  (`mdtests/byte_representation_const_destination_rejected.md`).
- `examples/label-build-flags/label_copy.click` specifies and verifies
  `label_copy`, and the README and the own-project guide
  (`docs/concepts/own-project.md`) no longer show the refusal.
