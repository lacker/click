# A plain-`char` `cstr_readable` requirement does not reach a callee

Soundness: incomplete. Click refuses a call whose precondition the caller
states verbatim; nothing false is accepted.

A caller that requires `cstr_readable(src)` must be able to call a function
that requires `cstr_readable(src)` with the same pointer, unchanged. Under the
default user-space target, where plain `char` is signed, this fails for a
`const char *` parameter. The identical pair with `const unsigned char *`
verifies, and passing the plain-`char` requirement to `strlen` works
(`mdtests/cstr_caller_requirement_reaches_return_calls_and_copies.md`,
`mdtests/c_builtin_string_header_declares_strlen.md`).

Reproduced on master `8ab87b3`:

```c filename=measure.c
#include <string.h>

unsigned long measure(const char *src)
{
	return strlen(src);
}

unsigned long outer(const char *src)
{
	unsigned long n = measure(src);
	return n;
}
```

```click
verifying "measure.c";

uint64 measure(const char* src) {
    requires cstr_readable(src);
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}

uint64 outer(const char* src) {
    requires cstr_readable(src);
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}
```

`measure` verifies; `outer` is refused at the call:

```text
proof error:
  `outer.contract` tactic 0
  `execute()` is missing prerequisite (measure precondition)
  (∃len:CMachineInteger(UInt64). uint64 <=(uint64((len+1u64)), 9223372036854775807u64) is true ⇒ ∃len:CMachineInteger(UInt64). (... ∀bound A:CMachineInteger(UInt64). (uint64 <(bound A, len) is true ⇒ int32 =(int8(load B=read<UInt8>(snapshot#2, pointer=value#1)), 0) is false)) ...))
  ...
  snapshot#2 = initial empty memory
```

The required form reads the bytes through `int8(...)` at `snapshot#2`, the
initial empty memory, rather than at the caller's entry snapshot where its own
requirement holds. Replacing `char` with `unsigned char` (and `char*` with
`uint8*` in the sidecar) makes both proofs verify.

Found while writing `examples/label-build-flags/`: a natural `label_copy`
that calls its sibling `label_measure(src)` on a `const char *src` hits this
refusal before reaching its `memcpy`. The example's `label_copy` calls
`strlen` directly, as written.

Intended regression: an mdtest with the source above whose `expect` block is
`pass`.

Acceptance criteria:

- The caller's `cstr_readable(src)` over a plain-`char` pointer discharges the
  callee's identical precondition under `x86_64-linux-userspace`.
- The same holds for `signed char` and under `x86_64-linux-kernel` where the
  header set allows it, and a caller without the requirement is still refused.
