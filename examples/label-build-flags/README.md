# Label build flags

A synthetic two-file C library with an ordinary `Makefile`: the worked example
of [Verify a function in your own project](../../docs/concepts/own-project.md).
The C is written as a C programmer would write it and is not adapted to Click.

| File | Role |
| --- | --- |
| `Makefile` | The real build: `-Iinclude -DLABEL_CAPACITY=32` |
| `include/label_config.h` | `LABEL_CAPACITY`, default 16, overridden by `-D` |
| `label.h` | Public prototypes, beside the sources |
| `label_fit.c` | `label_fit`, which uses the configured capacity |
| `label_copy.c` | `label_measure` and `label_copy`, which call `strlen`, `memcpy`, and `label_fit` |
| `label_fit.click`, `label_fit.click.import.json` | Compiler import with the build's flags |
| `label_copy.click` | Direct mode with Click's `<string.h>` and an `extern` contract for `label_fit` |

`label_fit.click` proves that the result is below the build's capacity of 32
and never exceeds the input length. It needs a compiler import because
`label_config.h` is found only through `-Iinclude` and the capacity comes from
`-D`. `label_copy.click` proves that `label_measure` returns less than 32 for
any readable C string, assuming `strlen`'s library contract and the `extern`
contract for `label_fit`, which restates what `label_fit.click` proves. The two
files can't share one sidecar today: compiler imports supply no system
headers, and direct mode has no `-I` or `-D`.

`label_copy` is not specified yet. Its `memcpy(dst, src, n)` call with a
`const char *` source is refused
(`bugs/memcpy-refuses-a-const-source-pointer.md`); the C stays as written.

From this directory:

```sh
click import lock label_fit.click
click verify label_fit.click
click verify label_copy.click
```

`make` builds `liblabel.a` with a host compiler; Click does not use the
`Makefile`. The lock and `label_fit.i` are local outputs, refreshed by the
examples gate.
