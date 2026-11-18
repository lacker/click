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
if any, you already understand. `label_fit` calls nothing. Create a sidecar,
`label.click`, next to the sources. It names the C file it verifies and states
a claim; the C is not edited:

```click filename=label.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
}
```

`unsigned long` is `uint64` under Click's default target,
`x86_64-unknown-linux-gnu` in `userspace` mode; see
[Supported types](../reference/language/c.md#supported-types). The proof is
omitted: Click runs the C symbolically along every path and then closes each
postcondition from what execution established.

## Bring in the build flags

Run without any configuration, Click reads the C itself:

```console
$ click verify label.click
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
records the result. It is configured in `click.project.json` at the project's
root, the nearest directory above the sidecar that has one; the file declares
*units*, here one C unit for the library's sources. Copy the preprocessor flags
from the compile command: `-I`, `-iquote`, `-isystem`, `-D`, `-U`, and
`-include`. The language standard and optimization flags may repeat the fixed
profile, but other flags such as `-Wall` are refused. Copying the whole compile
command therefore fails:

```json filename=click.project.json
{
  "units": {
    "label": {
      "language": "c",
      "compiler": "/usr/bin/gcc",
      "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
      "args": ["-std=c11", "-O2", "-Wall", "-Iinclude", "-DLABEL_CAPACITY=32"],
      "sources": {
        "label_fit.c": {}
      }
    }
  }
}
```

```console
$ click import lock label.click
click: unit `label`: source `label_fit.c`: unsupported compiler argument 3 `-Wall`; only -D/-U/-I/-iquote/-isystem/-include are supported
```

The language standard and ABI come from the target's fixed profile. The
project uses `-O2` by default; its top-level `optimization` setting selects a
different level for every C unit. Here `-std=c11` and `-O2` are accepted because
they match that profile. Keep only the preprocessor flags:

```json filename=click.project.json
{
  "units": {
    "label": {
      "language": "c",
      "compiler": "/usr/bin/gcc",
      "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
      "args": ["-Iinclude", "-DLABEL_CAPACITY=32"],
      "sources": {
        "label_fit.c": {}
      }
    }
  }
}
```

Then lock the project and verify. `click import lock` prints nothing on
success; it writes the preprocessed `.click/label/label_fit.c.i` and
`click.project.lock.json`. Given a sidecar, it locks the sidecar's project:

```console
$ click import lock label.click
```

```console
$ click verify label.click
1 selected proof verified
```

Verification now reads the locked state without running GCC, so commit the
lock and `.click/` with the project. If you edit `label_fit.c` or
`include/label_config.h`, verification refuses the stale lock until you run
`click import lock` again. See
[`click import`](../reference/cli/import.md#project-units) for every field.

Some details of the configuration:

- The sidecar's `verifying "label_fit.c";` selects the unit source of that
  name. Paths in `args` and `sources` are relative to the unit's `root`, by
  default the project directory; a unit may instead read an external tree,
  such as a git submodule, in place.
- The target is the project's: without a `"target"` the project uses
  `x86_64-unknown-linux-gnu`, and without a `"mode"` it uses
  `userspace`. Linux kernel code uses `kernel` mode, selected by
  `"mode": "kernel"` in `click.project.json`, the same file whose
  `"runtime"` selects the modeled pthread runtime; see
  [Selecting a target](../reference/language/c.md#selecting-a-target).
- Click does not read a `Makefile` or a C `compile_commands.json`. Copy the
  flags by hand from `make -n` output or from the entry's `arguments` or
  `command`. (A `compilation_database` field exists only for
  [C++ imports](../reference/cli/import.md#preliminary-c-semantic-artifact).)
- GCC never reads your platform's libc headers. A `#include <string.h>`
  finds Click's own header, as in direct mode, after any `-I` or `-isystem`
  directory you list; see
  [Click's system headers](../reference/cli/import.md#clicks-system-headers).

## Write the contract and read a failure

A failing proof shows that the build flags reached the proof. Claim the
header's default capacity instead of the build's:

```click filename=label.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 16;
}
```

```console
$ click verify label.click
proof error:
  `ensures result < 16` failed for `label_fit.ensures_0` path 0
  unclosed goal
  result < 16; left side evaluated to 31u64, right side evaluated to 16
  proof context
  case: [length >= 32u64]

goal: false
  --> label.click:4:5
  4 |     ensures result < 16;
    |     ^^^^^^^

To get a trace:
  click verify --trace-proof label_fit label.click
```

Read it from the top. The source excerpt points to the failing claim,
`ensures result < 16`, on the path whose `case:` is
`length >= 32`, where the function returned `31`. The claim is false for this
build; that is ordinary proof development, not a Click problem.

A more useful contract also says the function never lengthens a label:

```click filename=label.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
}
```

```console
$ click verify label.click
1 selected proof verified
```

The omitted proof closes both claims: it runs the C, one path per arm of its
`if`, and closes each claim on each path. On the path with `length >= 32`,
the returned `31` is at most `length`. To make this arithmetic step explicit,
split the proof on that condition before the C runs, step each arm to
function exit, and state the step as a `have` on the path that needs it:

```click filename=label.click
verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
} by {
    if length >= 32u64 {
        step_until(function.exit);
        have result <= length by solve();
    } else {
        step_until(function.exit);
    }
}
```

```console
$ click verify label.click
1 selected proof verified
```

When a claim you believe is true does not close, check the claim first, then
try smaller explicit steps such as `have`, and run the suggested
`--trace-proof` command to see the facts each step added. The
[proof-failure triage guide](proof-failure-triage.md) gives the full order.

## Calls to libc and to other files

`label_measure` in `label_copy.c` calls `strlen` from libc and `label_fit` from
the other file. The `Makefile` compiles `label_copy.c` with the same flags, so
add it to the unit as a second source; the unit's `args` apply to both:

```json filename=click.project.json
{
  "units": {
    "label": {
      "language": "c",
      "compiler": "/usr/bin/gcc",
      "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
      "args": ["-Iinclude", "-DLABEL_CAPACITY=32"],
      "sources": {
        "label_fit.c": {},
        "label_copy.c": {}
      }
    }
  }
}
```

Then name it in the sidecar and state `label_measure`'s contract:

```click filename=label.click
verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
} by {
    if length >= 32u64 {
        step_until(function.exit);
        have result <= length by solve();
    } else {
        step_until(function.exit);
    }
}

uint64 label_measure(const char* src) {
    let n: uint64;
    views click::cstr::cstr_at(src, n);
    ensures result < 32;
    ensures result <= n;
}
```

```console
$ click import lock label.click
```

```console
$ click verify label.click
assumptions: label_measure -> C library: strlen
2 selected proofs verified
```

### Libc calls

`label_copy.c` includes `<string.h>`. Click supplies its own
declaration-only system headers and checks each call against its own contract
for the function; GCC finds them in place of the platform's. The modeled
headers are `<stdint.h>`, `<inttypes.h>`, `<stdbool.h>`, `<limits.h>`,
`<stddef.h>`, `<string.h>` (`memcpy`, `memcmp`, `memset`, `strlen`), and
`<stdlib.h>` (`malloc`, `calloc`, `realloc`, `free`),
`<stdio.h>` (`FILE` and `stdout`), and the type-only
`<stdarg.h>` (`va_list`) and `<sys/types.h>` (`ssize_t`, `off_t`); the
[system headers](../reference/language/c.md#system-headers) table has the
details. Any other system include, such as `<ctype.h>`, stops
`click import lock` with a message that names it. Had `label_copy.c` begun
with `#include <ctype.h>`, the lock would fail with:

```text
click: unit `label`: preprocess label_copy.c: compiler exited with exit status: 1: In file included from label_copy.c:1:
<click>/ctype.h:2:2: error: #error "<ctype.h> is not one of Click's modeled system headers for x86_64-unknown-linux-gnu (userspace); see docs/reference/language/c.md#system-headers"
    2 | #error "<ctype.h> is not one of Click's modeled system headers for x86_64-unknown-linux-gnu (userspace); see docs/reference/language/c.md#system-headers"
      |  ^~~~~
```

The contracts are in the [standard library](../reference/library/index.md).
`strlen` views a C string, `views cstr_at(bytes, n)` at the contract value
parameter `let n: uint64;`, and returns its length `n`. The caller must hold
the string: `label_measure` declares its own `let n: uint64;`, views
`cstr_at(src, n)` itself and names the length `n`, which the C signature does
not carry, so its postcondition can compare the result with it.
`assumptions` lists every contract the result depends on but did not check,
by family: here, Click's `strlen` contract.

### Calls into other project functions

A call to another project function applies that function's contract, so
`label_measure`'s proof uses `label_fit`'s verified `ensures result < 32`
rather than re-executing its body. That is why both files are in one sidecar:
Click must see a function to verify a call to it. With only `label_copy.c`
in the sidecar, the same proof stops with
``no C source defines `label_fit` ``.

A function whose body is outside the program you verify, such as one from
another library, gets an `extern` contract instead: an `extern` block states
its contract without a body. Callers must establish its `requires`, Click
assumes its `ensures` without checking any implementation, and `click verify`
lists it among the `extern` assumptions. See
[External function contracts](../reference/language/c.md#external-function-contracts).

## What to do when Click refuses a construct

Try the remaining function, `label_copy`:

```click filename=label.click
import click::bytes;
import click::cstr;
import click::separation;

verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
    ensures length < 32u64 implies result == length;
    ensures 32u64 <= length implies result == 31u64;
}

uint64 label_measure(const char* src) {
    let n: uint64;
    views cstr_at(src, n);
    ensures n < 32u64 implies result == n;
    ensures 32u64 <= n implies result == 31u64;
}

uint64 label_copy(char* dst, const char* src) {
    let len: uint64;
    views cstr_at(src, len);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..len + 1u64]));
    ensures len < 32u64 implies result == len;
    ensures 32u64 <= len implies result == 31u64;
    ensures dst[result] == '\0';
    ensures bytes::equal(dst, 0u64, src, 0u64, result);
} by {
    step();
    step();
    step();
    step();
    have 0u64 <= n by { normalize(); }
    have n < 32u64 by { solve(); }
    have contains(memory(dst[0u64..32u64]), memory(dst[n])) by {
        apply(separation::contains_element(dst, 0u64, 32u64, n)) using { 0u64 <= n; n < 32u64; };
    }
    have separate(memory(dst[n]), memory(src[0u64..len + 1u64])) by { solve(); }
    open(cstr_at(src, len)) {
        step();
        mark copied;
        unfold(at(copied, bytes::equal(dst, 0u64, old(src), 0u64, n)));
        step();
        have bytes::equal(dst, 0u64, src, 0u64, n) by {
            unfold(bytes::equal(dst, 0u64, src, 0u64, n));
            transport(
                at(copied, (0u64..n).all(|k| {
                    (dst as (uint8 *))[0u64 + k] == old((src as (uint8 *))[0u64 + k])
                })),
                (0u64..n).all(|k| { (dst as (uint8 *))[0u64 + k] == (src as (uint8 *))[0u64 + k] })
            );
        }
        step_until(function.exit);
    }
}
```

`label_fit` now states exactly what it returns, and `label_measure` and
`label_copy` state exactly which length they keep: the whole string when it
fits, 31 bytes otherwise. The omitted
proof of `label_fit` proves its two new claims: on each path of
the C branch it refutes the claim's other hypothesis, such as `length < 32u64`
where `length >= 32`. The sidecar imports `click::cstr` for
`cstr_at`; see [Click library imports](sidecars.md#click-library-imports).
`label_copy` opens the string it views to lend a prefix of its bytes to
`memcpy`. `memcpy` owns its destination and views its source, and a call
cannot lend overlapping bytes both ways, so the copy needs a separate
destination and source. `label_copy` owns `dst` and views the string, which
keeps them apart, and its contract also states the separation over the
string's own bytes, `src[0u64..len + 1u64]`. Its value parameter is `len`,
not `n`, because the C body declares a local `n`. Its source may be `const`, as
in the existing C. The destination's 32-byte ownership and `label_fit`'s bound
also cover the terminator store.

`label_copy` also states the bytes it copied,
`bytes::equal(dst, 0u64, src, 0u64, result)`, which needs `import
click::bytes`. `memcpy` states them about the memory right after the call; the
proof marks that point `copied`, steps over the terminator store, and
`transport`s the unfolded fact to the current memory as a `have` over `n`.
The frame check assumes the fact's guard `k < n` for each read: `dst[k]` is
below the store at `dst[n]`, and `src[k]` is kept apart from `dst` by the
`separate` requirement. The final `step_until(function.exit);` runs the
return while the string is still open, so the scope's closing fold uses the
returned state. The implicit tail then closes
the postconditions, where `result` is `n`. The casts to `uint8*` read the bytes as `bytes::equal` does.
Verify this complete sidecar with `click verify label.click`.

Three kinds of report look different:

- **The source is outside what Click reads.** Click stops before any proof
  runs, naming a file and line: an unsupported system header, `failed to parse
  C source`, or `failed to process C source includes`. A compiler import that
  hits it fails at `click import lock` or when the locked source is loaded.
- **Click can't apply its model to an operation.** The proof's execution,
  named `step()` in the report, says it `could not verify C operation` and
  names the C statement. No contract change
  helps when the operation itself is outside the modeled subset.
- **A proof failure.** An `unclosed goal`, or the execution reporting a
  `missing prerequisite` or `undefined behavior`, names a claim or requirement that the
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
  and keep the supported functions verified.
- **Report the gap with the original source.** A construct the documentation
  says is supported, or an execution refusal like this one for a modeled
  function, is a Click bug. An unsupported construct outside the documented
  subset is missing
  functionality. Either way, include the smallest C that shows it, unchanged
  in shape, as [What to put in an issue](proof-failure-triage.md#what-to-put-in-an-issue)
  describes.

## Summary

- Put a sidecar next to the C files with a `verifying "file.c";` line per
  file and leave the C as it is.
- Use direct mode when quoted includes resolve beside their includers and no
  `-D` matters; otherwise copy `-I`, `-iquote`, `-isystem`, `-D`, `-U`, and
  `-include` into a C unit of `click.project.json` that lists the files, and
  run `click import lock`. Either way `<string.h>` and the other modeled
  system headers are Click's.
- Libc calls use Click's modeled headers and contracts; calls between project
  functions use the callee's verified contract; a function outside the
  program gets an `extern` contract. `click verify` reports the unchecked
  contracts as assumptions.
- Read a failure by its step: a refused source or operation is a coverage
  question; an unclosed goal or missing prerequisite is a proof question.
