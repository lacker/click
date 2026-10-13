# Verify a function in your own project

This guide takes a small C library with a `Makefile`, an include directory, a
`-D` build setting, and calls into libc and into another file, and verifies
functions in it without changing its C. It assumes you have read
[Your first proof](first-proof.md).

The project is checked in as `examples/label-build-flags/`, and every command
on this page is rerun by `tests/examples.rs` with the output shown here.

<!-- The sessions on this page are rerun by
     tests/examples.rs::own_project_guide_sessions_match_the_label_example. -->

## The project

The library stores short text labels in fixed-size buffers. Its build passes a
preprocessor search path and a capacity setting:

```make filename=Makefile
CPPFLAGS = -Iinclude -DLABEL_CAPACITY=32
CFLAGS = -std=c11 -O2 -Wall -Wextra

liblabel.a: label_fit.o label_copy.o
	$(AR) rcs $@ $^

label_fit.o label_copy.o: label.h
label_fit.o: include/label_config.h

clean:
	rm -f liblabel.a *.o
```

`make` compiles each file with a command like this one:

```text
cc -std=c11 -O2 -Wall -Wextra -Iinclude -DLABEL_CAPACITY=32  -c -o label_fit.o label_fit.c
```

The capacity has a default in a configuration header, which the build
overrides:

```c filename=include/label_config.h
/* Build-time configuration. The Makefile overrides it with -D. */
#ifndef LABEL_CONFIG_H
#define LABEL_CONFIG_H

#ifndef LABEL_CAPACITY
#define LABEL_CAPACITY 16
#endif

#endif
```

The public header sits next to the sources:

```c filename=label.h
#ifndef LABEL_H
#define LABEL_H

unsigned long label_fit(unsigned long length);
unsigned long label_measure(const char *src);
unsigned long label_copy(char *dst, const char *src);

#endif
```

`label_fit.c` uses the configured capacity:

```c filename=label_fit.c
#include "label_config.h"
#include "label.h"

/* The longest label that fits a LABEL_CAPACITY buffer with its NUL. */
unsigned long label_fit(unsigned long length)
{
	if (length >= LABEL_CAPACITY)
		return LABEL_CAPACITY - 1;
	return length;
}
```

`label_copy.c` calls `strlen`, `memcpy`, and `label_fit` from the other file:

```c filename=label_copy.c
#include <string.h>
#include "label.h"

/* How many bytes of src label_copy keeps. */
unsigned long label_measure(const char *src)
{
	return label_fit(strlen(src));
}

/* Copy src into a LABEL_CAPACITY buffer, truncating, and terminate it. */
unsigned long label_copy(char *dst, const char *src)
{
	unsigned long n = label_fit(strlen(src));

	memcpy(dst, src, n);
	dst[n] = '\0';
	return n;
}
```

## Pick a function and add a sidecar

Start with a leaf: a function whose behavior you can state and whose callees,
if any, you already understand. `label_fit` calls nothing. Create
`label_fit.click` next to `label_fit.c`. It names the C file and states a
claim; the C is not edited:

```click filename=label_fit.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
} by {
    execute();
    simp();
}
```

`unsigned long` is `uint64` under Click's default target,
`x86_64-linux-userspace`; see
[Supported types](../reference/language/c.md#supported-types). The proof
`execute(); simp();` runs the C symbolically along every path and then closes
each postcondition from what execution established.

## Bring in the build flags

Run without any configuration, Click reads the C itself:

```console
$ click verify label_fit.click
click: failed to read `label_config.h`: No such file or directory (os error 2)
```

This direct mode is a bounded preprocessor. It resolves a quoted
`#include "file.h"` relative to the file that includes it, supplies its own
[system headers](../reference/language/c.md#system-headers), and takes no
command-line flags: there is no `-I` and no `-D`. A file whose quoted includes
are all found next to it, and whose meaning does not depend on a `-D` setting,
needs nothing more. `label_fit.c` needs both, so it needs a compiler import.

> **Note:** A header default such as `#ifndef LABEL_CAPACITY` makes this
> trap easy to miss. When a direct-mode file finds the header, Click proves the
> code with the header's default, `16`, not the build's `32`.

A compiler import runs GCC's preprocessor with flags you list, once, and
records the result. Its configuration is a JSON file named after the sidecar.
Copy the preprocessor flags from the compile command: `-I`, `-isystem`, `-D`,
`-U`, and `-include`. Other flags are refused, so copying the whole command
line fails:

```json filename=label_fit.click.import.json
{
  "schema": 1,
  "target": "x86_64-linux-userspace",
  "compiler": "/usr/bin/gcc",
  "working_directory": ".",
  "environment": {
    "allow": {
      "PATH": "/usr/bin:/bin",
      "LC_ALL": "C"
    }
  },
  "sources": [
    {
      "logical_source": "label_fit.c",
      "path": "label_fit.c",
      "args": ["-std=c11", "-O2", "-Iinclude", "-DLABEL_CAPACITY=32"],
      "artifact": "label_fit.i"
    }
  ]
}
```

```console
$ click import lock label_fit.click
click: source `label_fit.c`: unsupported compiler argument 2 `-O2`; only -D/-U/-I/-isystem/-include are supported
```

The language standard and the ABI come from the target's fixed profile, so
`-std=c11` is accepted only because it matches it. Keep only the
preprocessor flags:

```json filename=label_fit.click.import.json
{
  "schema": 1,
  "target": "x86_64-linux-userspace",
  "compiler": "/usr/bin/gcc",
  "working_directory": ".",
  "environment": {
    "allow": {
      "PATH": "/usr/bin:/bin",
      "LC_ALL": "C"
    }
  },
  "sources": [
    {
      "logical_source": "label_fit.c",
      "path": "label_fit.c",
      "args": ["-Iinclude", "-DLABEL_CAPACITY=32"],
      "artifact": "label_fit.i"
    }
  ]
}
```

Then lock the import and verify. `click import lock` prints nothing on
success; it writes the preprocessed `label_fit.i` and
`label_fit.click.import.lock.json`:

```console
$ click import lock label_fit.click
```

```console
$ click verify label_fit.click
1 selected proof verified
```

Verification now reads the locked snapshot without running GCC. If you edit
`label_fit.c` or `include/label_config.h`, verification refuses the stale lock
until you run `click import lock` again. See
[`click import`](../reference/cli/import.md#configure-and-lock-an-import) for
every field.

Some details of the configuration:

- Paths in `args` are relative to `working_directory`, which is relative to
  the configuration file.
- `target` must agree with the sidecar's target. Without a `target`
  directive the sidecar uses `x86_64-linux-userspace`. Linux kernel code uses
  `x86_64-linux-kernel`, selected by a `target "x86_64-linux-kernel";`
  directive or by a `click.project.json` such as
  `{"target":"x86_64-linux-kernel"}` beside the sidecars. The same file
  selects the modeled pthread runtime; see
  [Selecting a target](../reference/language/c.md#selecting-a-target).
- Click does not read a `Makefile` or a C `compile_commands.json`. Copy the
  flags by hand from `make -n` output or from the entry's `arguments` or
  `command`. (A `compilation_database` field exists only for
  [C++ imports](../reference/cli/import.md#preliminary-c-semantic-artifact).)
- Compiler mode passes `-nostdinc` and supplies no system headers, neither
  the platform's nor Click's own. A file that includes `<string.h>`,
  `<stddef.h>`, or `<stdint.h>` fails at `click import lock` with GCC's
  `No such file or directory`. Today a file that needs both `-I`/`-D` and a
  system header can't be verified unchanged; see
  [What to do when Click refuses a construct](#what-to-do-when-click-refuses-a-construct).

## Write the contract and read a failure

A failing proof shows that the build flags reached the proof. Claim the
header's default capacity instead of the build's:

```click filename=label_fit.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 16;
} by {
    execute();
    simp();
}
```

```console
$ click verify label_fit.click
proof error:
  `label_fit.contract` path 0, tactic 1
  checked outcome `simp` search did not retain a complete proof for `label_fit.ensures_0`
  `label_fit.contract` proof step tactic 1
  `ensures result < 16` failed for `label_fit.ensures_0` path 0
  unclosed goal
  result < 16; left side evaluated to 31u64, right side evaluated to 16
  proof context
  case: [length >= 32u64]

tactic@7:
  simp();

To get a trace:
  click verify --trace-proof label_fit label_fit.click
```

Read it from the top. `tactic 1` is `simp()`, the second step of the proof, so
execution succeeded and the C has no undefined behavior on this path. The
failing claim is `ensures result < 16` on the path whose `case:` is
`length >= 32`, where the function returned `31`. The claim is false for this
build; that is ordinary proof development, not a Click problem.

A more useful contract also says the function never lengthens a label:

```click filename=label_fit.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
} by {
    execute();
    simp();
}
```

```console
$ click verify label_fit.click
proof error:
  `label_fit.contract` path 0, tactic 1
  checked outcome `simp` search did not retain a complete proof for `label_fit.ensures_1`
  `label_fit.contract` proof step tactic 1
  `ensures result <= length` failed for `label_fit.ensures_1` path 0
  unclosed goal
  result <= length; left side evaluated to 31u64, right side evaluated to length
  proof context
  case: [length >= 32u64]

tactic@8:
  simp();

To get a trace:
  click verify --trace-proof label_fit label_fit.click
```

This claim is true: on that path `length >= 32`, so `31 <= length`. The miss
is `simp()`'s, a bounded search whose arithmetic step handles `int32` goals,
while this one is a 64-bit `unsigned long` comparison. State the fact with
`have ... by auto`, which carries machine comparisons to integer arithmetic and
solves them:

```click filename=label_fit.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
} by {
    execute();
    have result <= length by auto;
    simp();
}
```

```console
$ click verify label_fit.click
1 selected proof verified
```

When a claim you believe is true does not close, check the claim first, then
try smaller explicit steps such as `have`, and run the suggested
`--trace-proof` command to see the facts each step added. The
[proof-failure triage guide](proof-failure-triage.md) gives the full order.

## Calls to libc and to other files

`label_measure` in `label_copy.c` calls `strlen` and `label_fit`. `label_copy.c`
needs no `-I` or `-D` (`label.h` is beside it), and it includes `<string.h>`,
so it uses direct mode with no import configuration.

### Libc calls

Click supplies its own declaration-only system headers for the user-space
target and checks each call against its own contract for the function. The
modeled headers are `<stdint.h>`, `<inttypes.h>`, `<stdbool.h>`, `<limits.h>`,
`<stddef.h>`, `<string.h>` (`memcpy`, `memcmp`, `memset`, `strlen`),
`<stdlib.h>` (`malloc`, `calloc`, `realloc`, `free`), `<pthread.h>`, and
`<stdatomic.h>`; the [system headers](../reference/language/c.md#system-headers)
table has the details. Any other system include, such as `<ctype.h>` or
`<stdio.h>`, stops verification of that file before any proof runs:

```text
click: failed to process C source includes: label_copy.c:1: system header `<ctype.h>` is not supported
```

The contracts are in the [standard library](../reference/library/index.md).
`strlen` requires `cstr_readable(src)`: a readable, NUL-terminated string. The
caller must state that requirement.

### Calls into other project functions

A call to another project function uses that function's contract when it has
one, and otherwise executes its body. Either way Click needs to see the
function. Without `label_fit.c` in this sidecar, the call has nothing to apply:

```click filename=label_copy.click
verifying "label_copy.c";

uint64 label_measure(const char* src) {
    requires cstr_readable(src);
    ensures result < 32;
} by {
    execute();
    simp();
}
```

```console
$ click verify label_copy.click
proof error:
  no C source defines `label_fit`
```

There are two ways to supply it:

- **Verify the callee in the same sidecar.** Add `verifying "label_fit.c";`
  and its contract and proof. A call then applies that verified contract. This
  works when both files can be read in the same mode, all in direct mode or
  all in one compiler import (a `sources` entry per file).
- **Give the callee an `extern` contract.** An `extern` block states a
  contract for a function whose body is outside the sidecar. Callers must
  establish its `requires`, and Click assumes its `ensures` without checking
  any implementation.

Here `label_fit.c` needs the build flags and `label_copy.c` needs
`<string.h>`, so they can't share a mode, and `label_copy.click` uses an
`extern` contract that restates what `label_fit.click` proves:

```click filename=label_copy.click
verifying "label_copy.c";

extern uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
}

uint64 label_measure(const char* src) {
    requires cstr_readable(src);
    ensures result < 32;
} by {
    execute();
    simp();
}
```

```console
$ click verify label_copy.click
external assumptions: label_measure -> label_fit, strlen
2 selected proofs verified
```

`external assumptions` lists every contract the result depends on but did not
check. `strlen` is Click's libc contract. `label_fit` is your `extern` block:
Click does not connect it to `label_fit.click`, so keep the two in agreement
by hand, and verify `label_fit.click` as well.

## What to do when Click refuses a construct

Try the remaining function, `label_copy`:

```click filename=label_copy.click
verifying "label_copy.c";

extern uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
}

uint64 label_measure(const char* src) {
    requires cstr_readable(src);
    ensures result < 32;
} by {
    execute();
    simp();
}

uint64 label_copy(char* dst, const char* src) {
    requires cstr_readable(src);
    owns dst[0..32];
    ensures result < 32;
    ensures dst[result] == '\0';
} by {
    execute();
    simp();
}
```

```console
$ click verify label_copy.click
proof error:
  `label_copy.contract` tactic 0
  `execute()` could not verify C operation
  function contract could not be applied
  could not bind arguments for memcpy
  C operation
  memcpy(dst, src, n)
  call bindings
  destination = dst, source = src, bytes = n
  C statement at label_copy.c:15:2
  `memcpy(dst, src, n);`

tactic@22:
  execute();

To get a trace:
  click verify --trace-proof label_copy label_copy.click
```

Three kinds of report look different:

- **The source is outside what Click reads.** Click stops before any proof
  runs, naming a file and line: an unsupported system header, `failed to parse
  C source`, or `failed to process C source includes`. A compiler import that
  hits it fails at `click import lock` or when the locked source is loaded.
- **Click can't apply its model to an operation.** `execute()` reports that it
  `could not verify C operation` and names the C statement. No contract change
  helps when the operation itself is refused, as here, where the arguments are
  not bound to the `memcpy` contract at all.
- **A proof failure.** An `unclosed goal`, or `execute()` reporting a `missing
  prerequisite` or `undefined behavior`, names a claim or requirement that the
  facts did not establish. Change the contract or the proof.

For the first two, look the construct up in
[language coverage](../reference/coverage.md), which gives the status of each
C, C++, and Rust feature, and in [Supported C](../reference/language/c.md),
whose
[unsupported list](../reference/language/c.md#unsupported-or-easy-to-forget-c)
names common gaps. Then:

- **Don't rewrite correct C to suit the verifier.** Dropping `const` from
  `src`, or copying bytes in a loop instead of calling `memcpy`, would prove a
  different program from the one you ship. Click's policy is that
  [existing C is the boundary](../index.md#existing-c-is-the-boundary):
  adaptations go in contracts, proofs, or Click itself, and the C changes only
  for a real bug or an independently wanted change.
- **Verify what you can.** Leave the refused function out of the sidecar,
  as `examples/label-build-flags/label_copy.click` does, and keep the rest
  verified.
- **Report the gap with the original source.** A construct the documentation
  says is supported, or an `execute()` refusal like this one for a modeled
  function, is a Click bug; this one is filed as
  [`memcpy` refuses a `const` source pointer](https://github.com/clicklang/click/blob/master/bugs/memcpy-refuses-a-const-source-pointer.md).
  An unsupported construct outside the documented subset is missing
  functionality. Either way, include the smallest C that shows it, unchanged
  in shape, as [What to put in an issue](proof-failure-triage.md#what-to-put-in-an-issue)
  describes.

## Summary

- Put a sidecar next to the C file with `verifying "file.c";` and leave the C
  as it is.
- Use direct mode when quoted includes resolve beside their includers and no
  `-D` matters; otherwise copy `-I`, `-isystem`, `-D`, `-U`, and `-include`
  into `FILE.click.import.json` and run `click import lock`. Today, a file
  can't have both flags and system headers.
- Libc calls use Click's modeled headers and contracts; other project
  functions are verified in the same sidecar or given `extern` contracts,
  which `click verify` reports as external assumptions.
- Read a failure by its step: a refused source or operation is a coverage
  question; an unclosed goal or missing prerequisite is a proof question.
