# click

`click` is a new programming language.

Click's goal is to make it easy to prove things about programs in other
programming languages. Starting with C.

## Kernel design

There's a traditional principle of theorem prover design that says you should
build a small, trusted kernel.

The traditional rationale is that to build a huge bug-free structure, you need the
heart of it to be bug-free. You can only do that by close inspection.
Close inspection is hard, so you want it to be really small.
Then you prove things outward from there.

I claim that for the task of "systems engineering theorem proving", this
is actually the wrong design.

Instead, you should put a lot of domain-specific machinery into the kernel.
It is a good idea to have many data structures and axioms that are specific
to systems engineering.
The rationale is that it lets people develop faster.
It lets you put more powerful tactics in the kernel, and it makes performance
better.
These are important for the systems engineering questions that we care about.
Like, can we formally verify Linux.

There's a serious tradeoff!
The downside is that you are more likely to have bugs in the kernel.
But, for our domain, this is not the most important problem.
We aren't concerned about the soundness of mathematics itself.
We are verifying code that is already supposed to work.
When we discover bugs in the kernel, we don't have a huge tower of false
statements that we became dependent on.
It isn't going to lead to some sort of philosophical disaster.

We should certainly fix bugs in the kernel when we find them.
But it isn't the priority during development, for the Click kernel to be simple.
It should be fast on big codebases.
It should be powerful, ie, really good at proving things.
Those are the priorities.

In other words, we are happy to hardcode axioms and tactics
about char*, float64, or malloc into the kernel.

## Only humans may edit the content above this point. AIs may edit below this point.

## Hello, world

Click checks C against a contract in a separate `.click` file. Start with
the original hello-world program from Kernighan and Ritchie.

```c filename=hello.c
#include <stdio.h>

main()
{
    printf("hello, world\n");
}
```

```click filename=hello.click
verifying "hello.c";
import click::c::stdio::{stream, write_requests};

function greeting() -> List<uint8> {
    List::Cons('h', List::Cons('e', List::Cons('l', List::Cons('l',
    List::Cons('o', List::Cons(',', List::Cons(' ', List::Cons('w',
    List::Cons('o', List::Cons('r', List::Cons('l', List::Cons('d',
    List::Cons('\n', List::Nil)))))))))))))
}

int32 main() {
    owns out: stream(stdout);
    ensures write_requests(out.write_history) == List::Cons(greeting(), List::Nil);
} by {
    unfold(greeting());
    unfold(write_requests(List<WriteAttempt>::Nil));
}
```

```console
$ click verify hello.click
assumptions: main -> printf: "hello, world\n"
2 selected proofs verified
```

Click supplies an open `stdout` stream at program startup. The contract
checks that `main` makes one write attempt with the exact greeting, including
the newline. A successful `printf` reports that the stream accepted all 13
bytes. An I/O error can leave partial output, and buffered output can still
fail when flushed. The C program ignores the return value.

Try changing a letter in the C program and running Click again. The proof
fails because the requested bytes differ from the contract.

[Example files](examples/hello-world/)

## Verify a return value

```c filename=clamp.c
int clamp(int x, int lo, int hi) {
    if (x < lo) {
        return lo;
    }
    if (x > hi) {
        return hi;
    }
    return x;
}
```

```click filename=clamp.click
verifying "clamp.c";

int32 clamp(int32 x, int32 lo, int32 hi) {
    requires lo <= hi;
    ensures lo <= result and result <= hi;
    ensures lo <= x and x <= hi implies result == x;
}
```

```console
$ click verify clamp.click
1 selected proof verified
```

The sidecar says that whenever `lo <= hi`, `clamp` returns a value in
`[lo, hi]`, and returns `x` unchanged when it is already in range. Click also
proves that the call has no undefined behavior. The omitted proof
runs the function and closes both claims.
Delete the `requires` line and verification fails: Click reports the
`x < lo` path, where `lo` is returned even though it can exceed `hi`.

These files are [`examples/clamp/`](examples/clamp/). Next, read
[Your first proof](docs/concepts/first-proof.md) and
[What Click proves](docs/concepts/what-click-proves.md).

## Install Click

No Click release has been published yet, so build the command from a checkout
of this repository:

```sh
cargo install --path . --bin click
```

The installers below fetch published GitHub releases. Until the first release
is tagged they report that no release exists. On macOS or Linux, install the
latest release with:

```sh
curl --proto '=https' --tlsv1.2 -LsSf https://raw.githubusercontent.com/clicklang/click/master/install.sh | sh
```

Set `CLICK_VERSION` to install a specific release instead:

```sh
curl --proto '=https' --tlsv1.2 -LsSf https://raw.githubusercontent.com/clicklang/click/master/install.sh | CLICK_VERSION=0.1.0 sh
```

On Windows, run the matching PowerShell installer. It installs the latest
release by default and also accepts `CLICK_VERSION`:

```powershell
irm https://raw.githubusercontent.com/clicklang/click/master/install.ps1 | iex
```

```powershell
$env:CLICK_VERSION = '0.1.0'; irm https://raw.githubusercontent.com/clicklang/click/master/install.ps1 | iex
```

The `clicklang` crate is not published to crates.io.

Click keeps its launcher and installed versions under `~/.click`. The launcher
uses the nearest `.click-version` file for a project, then the global default.
`click upgrade` installs the latest release and makes it the global default.
Use `click version add 0.1.0` to add a specific version, `click version use 0.1.0`
to pin the current directory for the project, and `click version default 0.1.0`
to change the global fallback. Without either, Click runs the launcher version.
`click version list` lists installed versions, and `click version remove 0.1.0`
removes one.

C is built in. `click add cpp` and `click add rust` add the C++ and Rust front
ends, which prepare compiler imports (C++ on Linux x86-64 and macOS arm64,
Rust on Linux x86-64), to the version that
runs; `click languages` lists them. A new version from `click upgrade` or
`click version add` gets the same languages. To add them while installing, set
`CLICK_LANGUAGES`:

```sh
curl --proto '=https' --tlsv1.2 -LsSf https://raw.githubusercontent.com/clicklang/click/master/install.sh | CLICK_LANGUAGES=cpp sh
``` A project can commit `.click-version` to share its pin with
collaborators.

Set `CLICK_HOME` to choose a different install directory. Set
`CLICK_RELEASE_REPOSITORY=owner/name` to install from another GitHub repository.

## Documentation

The AI reference lives in [docs/](docs/); start with
[Start here](docs/index.md). It is written for AI agents that use or develop
Click and is maintained by agents. The rendered reference also serves
`llms.txt` and a one-file bundle of the "Using Click" part. The human-written guide will live in
[guide/](guide/). Useful entry points:

- [What Click proves](docs/concepts/what-click-proves.md): what a verified
  claim means and what it assumes.
- [Frequently asked questions](docs/faq.md): setup, guarantees, coverage,
  proof failures, and contributions.
- [Your first proof](docs/concepts/first-proof.md): a guided first sidecar.
- [Language reference](docs/reference/language/index.md): complete `.click`
  syntax.
- [Proof-failure triage](docs/concepts/proof-failure-triage.md): what to do
  when a proof fails.
- [Upstream integrations](integrations/README.md): bounded, reproducible
  claims about unchanged projects, including Bitcoin Core's `MoneyRange`.

Build and serve the reference locally with `scripts/install-tools.sh` once,
then `scripts/mdbook-serve.sh` (it serves `http://localhost:3000`).

Preview the guide with `scripts/guide-serve.sh`, which needs Node.js and serves
`http://localhost:5173`. The site's configuration is in [site/](site/); its
pages are the Markdown files in `guide/`, with `guide/index.md` as the home
page.

Public documentation hosting is paused until the guide and reference are ready
to publish. The `site-preview` workflow builds them for validation only.
`scripts/build-site.sh` builds the guide at the root and the reference under
`reference/` locally into `target/click-pages`.

## Contributing

Click verifies existing C as written: a proof failure is not permission to
refactor working C into a verifier-friendly shape
([What Click proves](docs/concepts/what-click-proves.md#existing-c-comes-first)).
`scripts/check.sh` is the full gate that CI runs. Read the
[contribution workflow](docs/internals/contributing.md) before opening a pull
request; agents also follow [AGENTS.md](AGENTS.md).
