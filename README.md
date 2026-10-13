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

## Verify a C function

Click proves properties of existing C. You write the claims and proofs in a
`.click` sidecar next to the C; the C itself stays as it is.

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
} by auto;
```

```console
$ click verify clamp.click
1 selected proof verified
```

The sidecar says that whenever `lo <= hi`, `clamp` returns a value in
`[lo, hi]`, and returns `x` unchanged when it is already in range. Click also
proves that the call has no undefined behavior. `by auto` finds the proof.
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
Use `click install 0.1.0` to add a version, `click use 0.1.0` to pin the
current directory for the project, and `click default 0.1.0` to change the
global fallback. Without either, Click runs the launcher version. `click versions`
lists installed versions. A project can commit `.click-version` to share its
pin with collaborators.

Set `CLICK_HOME` to choose a different install directory. Set
`CLICK_RELEASE_REPOSITORY=owner/name` to install from another GitHub repository.

## Documentation

The technical documentation lives in [docs/](docs/); start with
[Click documentation](docs/index.md). It is AI-written; a human-written guide
will follow as a separate work. Useful entry points:

- [What Click proves](docs/concepts/what-click-proves.md): what a verified
  claim means and what it assumes.
- [Your first proof](docs/concepts/first-proof.md): a guided first sidecar.
- [Language reference](docs/reference/language/index.md): complete `.click`
  syntax.
- [Proof-failure triage](docs/concepts/proof-failure-triage.md): what to do
  when a proof fails.
- [Upstream integrations](integrations/README.md): bounded, reproducible
  claims about unchanged projects, including Bitcoin Core's `MoneyRange`.

Build and serve the site locally with `scripts/install-tools.sh` once, then
`scripts/mdbook-serve.sh` (it serves `http://localhost:3000`).

## Contributing

Click verifies existing C as written: a proof failure is not permission to
refactor working C into a verifier-friendly shape
([What Click proves](docs/concepts/what-click-proves.md#existing-c-comes-first)).
`scripts/check.sh` is the full gate that CI runs. Read the
[contribution workflow](docs/internals/contributing.md) before opening a pull
request; agents also follow [AGENTS.md](AGENTS.md).
