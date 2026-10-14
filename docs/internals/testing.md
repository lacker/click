# Testing Click

`tests/process_containment.rs` checks the CLI's independent crash watchdog.
The debug-only `CLICK_DEBUG_BLOCK_VERIFIER` hook parks the verifier after its
containment scope opens, without polling a deadline. The child must exit with
a containment message; an independent outer test bound kills a broken child.
A normal verification also checks cancellation of a long-lived watchdog.
The hook is omitted from release builds, and library tests retain cooperative
limits without process termination.

Click uses ordinary Rust tests plus markdown integration tests.

The [verification efficiency contract](verification-efficiency.md) is part of
correctness testing. In particular, an all-simple project must scale with the
selected source and explicit proof rather than with repeatedly copied or
scanned ambient state. Wall-clock profiling locates current pain; deterministic
multi-size regressions protect the scaling law.

Use [Triaging Proof Failures](../concepts/proof-failure-triage.md) to classify a failed
proof before deciding whether it belongs in a regression test, an issue, or
ordinary proof development. This page describes how to test and contain the
tooling failures identified by that process.

## Tooling failures block feature work

Treat the verifier and its proof tools as the foundation for every language
feature and example. If verification becomes unexpectedly slow without a local
bounded failure, a smart success cannot expand into verifiable source,
`click-expand` fails or emits an unverifiable rewrite, the performance tools disagree, or a normal
diagnostic dumps enormous internal state, stop feature work. Reduce and fix the
tooling defect first. If it cannot be fixed in the same chunk, record a focused
bug with a regression plan and return the branch to a green checkpoint before
continuing. New roadmap issues require an explicit user request.

Do not compensate by increasing a time limit, accepting eventual success,
rewriting the example into unnatural C, or adding irrelevant proof facts. Those
actions hide a foundation problem and make the next feature harder to debug.
The repository-level version of this rule is in `AGENTS.md`; filing procedures
are in `bugs/README.md` and `issues/README.md`.

A smart tactic that promptly reports that it did not find a proof is not one of
these tooling failures. Smart search is heuristic and incomplete. Continue
with a smaller search or explicit relevant simple tactics. During joint example
and verifier development, repeated misses still trigger the
[three-strikes investigation](../concepts/proof-failure-triage.md#three-strikes-during-example-development).
Investigate sooner if search misses its budget, produces an unusable diagnostic,
reports success without verifiable expansion, behaves unstably, or exposes a
missing simple proof operation.

Ordinary verifier errors are capped at 16 KiB of UTF-8 text. Fact and resource
lists show at most twelve entries and report how many were omitted. Engine
debugging that genuinely needs complete internal terms can opt in with
`CLICK_FULL_DIAGNOSTICS=1`; do not enable it in normal tests or user workflows.

CLI subcommands and fixture gates must call the shared bounded verification
engine directly. Do not implement them through recursive Click subprocesses,
hidden child modes, test-binary wrappers, stderr scraping, or shell redirect/move
recipes. OS process isolation is reserved for a narrow, owned crash-containment
boundary.

After a timeout or interrupted bounded run, confirm its verifier process tree
has exited before measuring another run. Profile a non-verifying target only
when diagnosing unexpected slowness or a timeout, and label it as an incomplete
diagnostic run. Establish correctness before optimizing; never expand a tactic
from an incomplete run.

Judge tests from the tested command's exit status, not the last line of its
output. When piping output, use `pipefail` or capture the command's status
explicitly; a successful `tail` is not a passing test. `cargo test --lib` omits
proof-fixture suites and cannot establish a green tree.

Run the full suite with:

```sh
scripts/check.sh
```

For a change limited to prose or documentation metadata, use the focused
documentation gate:

```sh
scripts/check.sh --docs-only
```

This renders the site, runs the advisory docs lint, and runs the
source-backed documentation test. It skips Rust formatting and Clippy, the
C++ exporter, library and binary unit tests, proof fixtures, examples, and
compiler-import fixtures. Do not use it for `mdtests/` changes: those Markdown
files are executable proof fixtures, not prose documentation. Code, scripts,
configuration, and example implementation changes also require the full gate.

The rendered site also serves `llms.txt` and `click-reference.md`, a bundle of
the "Using Click" pages, generated from `docs/SUMMARY.md` and the pages it
lists; they are not committed. The documentation test
`ai_reference_site_files_generate` generates them in memory, so a page whose
opening sentence is missing or ends in a colon, or a link the bundle can't
resolve, fails the gate with the page named. The docs-only gate writes them
into `target/click-docs/`; after a plain `scripts/mdbook-build.sh`, run
`scripts/build-ai-reference.sh`.

Run the markdown proof fixtures with:

```sh
cargo test --test mdtests
```

Run the larger example-project verifier with:

```sh
cargo test --test examples
```

## Compiler import fixtures

Rust proof regressions use locked native artifacts when their purpose is to
check lowering, claims, authority, or proof scaling. The inputs in
`design/charon-trial/gate-fixtures/` must match the unchanged test source;
missing or stale fixtures fail rather than trigger compiler extraction.
A separate nightly test re-extracts these inputs and compares native artifacts
after relocating the one absolute source-path metadata field. Live compiler rejection, crate-input identity, and reproducibility
checks remain real compiler tests in nightly. Whole-example profiling,
expansion, certificate rechecks, and audits have separate nightly tests, while
the positive and negative proof assertions stay in the normal gate.


On Linux, the gate runs `tests/compiler_import.rs` against GCC at
`/usr/bin/gcc`. `scripts/setup-environment.sh` installs GCC on Ubuntu 24.04;
provision it manually on other Linux distributions. Missing GCC fails the
preparation fixture; the gate never downloads a compiler or silently skips
these checks. The fixture creates artifacts and locks in an isolated
temporary directory, then checks offline loading, verification, and expansion.
On macOS, compiler-independent unit regressions load and verify a relocated C
artifact with no GCC or target headers installed, and reject changed source,
artifact, local header, and lock identity bytes. A committed artifact prepared
on Ubuntu with GCC additionally verifies and expands through the ordinary C
import path after relocation; its compiler backend is absent on macOS. It
includes only project-local headers: no fixture depends on a platform's
library headers for a standard interface, which Click supplies itself.

The pinned Linux `lib/rbtree.c` input closure in `integrations/linux-rbtree/`
is a negative gate fixture, checked by the library tests in
`src/languages/c/linux_rbtree_tests.rs`. The closure's archive and member
hashes are checked on every host. Reproducing the preprocessed artifact and
pinning the first rejection need the recorded GCC, identified by the hashes
of its driver and `cc1`; Ubuntu 24.04's GCC 13 package is that compiler. On
another compiler that part reports `linux-rbtree: NOT CHECKED` and passes,
unless `CLICK_LINUX_RBTREE_REQUIRE_TOOLCHAIN=1` is set. When a C frontend
change moves the pinned rejection, update the pin and the inventory in
`issues/kernel-scale-preprocessing.md` in the same change.

The Linux fixtures cover compiler conditional selection, token pasting and
macro rescanning, contextual headers, configured dependencies, refresh after
an optional header appears, stale configs, artifact tampering, import identity,
and original-source diagnostics. They do not claim that the complete captured
Linux translation unit verifies.

When the pinned toolchain is installed, the gate also builds
`tools/cpp-exporter/main.cpp` against exactly Clang and LLVM 19.1.7, then runs
`tests/cpp_import.rs` (see [frontend toolchains](#frontend-toolchains)). Set `LLVM_CONFIG` when the pinned
`llvm-config` is not installed in a standard versioned location. On macOS,
Homebrew's `llvm@19` package provides the expected toolchain. On Linux, Clang
borrows the C++ standard library headers of the newest GCC installation it
finds, so that installation's headers must be present too (on Debian and
Ubuntu, `libstdc++-N-dev` for the newest `/usr/lib/gcc/x86_64-linux-gnu/N`);
a distribution update that moves the libstdc++ runtime forward without its
headers is the usual cause of a sudden `<algorithm>` not found. The build
script checks this first and names the missing package. On Ubuntu 24.04,
`scripts/setup-environment.sh` installs the pinned development packages,
including those headers, before the network-free gate runs.

The C++ fixtures refresh typed artifacts for C++20 functions in a translation
unit or one selected included project header through one exact JSON
compilation-database entry, then make the exporter unavailable and load the
artifacts again. This checks the intended phase boundary: explicit refresh
executes Clang, while ordinary loading validates the config, compilation
database, translation unit, selected logical source, lock, and stored semantic
artifact. Focused failures cover a missing or ambiguous translation-unit
command, a non-Clang driver, a mismatched semantic profile, a changed command or
selected header, and an ambiguous or wrong-location header declaration.
They verify a linear mutable-reference function, a by-value-boolean branch with
an early return, a mutable/const reference pair that explicitly aliases one
owned cell, and a selected function that reaches another `noexcept` definition
through a resolved direct call. The call fixture checks modular contracts,
offline loading, expansion/reverification, and retained audit against the same
multi-function artifact. A scalar-local fixture captures that call's result,
copies it through an expression-initialized local, assigns it, and returns it
through the kernel's shared declaration and scalar rules. Its false-result
contract is rejected. Focused negative coverage rejects missing, throwing, and
recursive reachable definitions as well as uninitialized, reference-valued,
and nested locals. An exception-enabled header fixture omits `noexcept`, locks
the distinct Clang profile, and verifies offline under the artifact's
`normal_only` guarantee. Its focused checks reject `throw`, `try`/`catch`, an
unresolved reachable call, record/object use, and config/profile disagreement;
they do not claim exception-path support. A separate object-free `scalar_int32`
fixture locks a typed source throw, verifies the helper's exceptional claim,
and carries that outcome through a modular caller while its normal path
continues. It rejects an undeclared or false exceptional claim and a non-int32
payload. Kernel-only handler regressions now check that an exact int32 catch
binds the exceptional payload and thrown state across a verified modular call,
while normal returns bypass the handler and a throw from the handler escapes.
The binding must be fresh, so it cannot replace an existing local. A separate
C++ importer fixture locks one source `try`/`catch (int name)` over a modular
helper call and checks ordinary verification, expansion/reverification, audit,
and rejection of a false result claim. A focused importer regression checks that
function-scope destructors are emitted before rethrowing both explicit throws
and exceptions from call-initialized locals. Exceptional mutable postconditions
remain outside this profile. A signed-64 predicate fixture retains a direct `CAmount` typedef
identity, imports `const CAmount&`, the implicit
promotion of zero, signed `>=`, and a `bool` result, then verifies an exact
all-input contract offline. Its false zero-boundary contract fails, while
mutable and unsigned wide references and other relational operators fail at
the frontend boundary. A constexpr fixture locks a fixture-owned
`<cstdint>` dependency,
retains the two-link `CAmount`/`int64_t` alias chain, and imports one leaf
`static constexpr` signed-64 constant by declaration identity. Its exact
all-input comparison verifies offline; dependency tampering, an undeclared
dependency, mutable storage, and a non-leaf initializer fail locally. A second
fixture retains the ordered `COIN`/`MAX_MONEY` graph, validates the one signed
64-bit multiplication against Clang's evaluated value, and verifies a
`MAX_MONEY` comparison offline. It rejects a third constant, a different
initializer operator, and runtime multiplication. A second selection verifies
the inclusive signed-64 `value <= MAX_MONEY` upper bound and rejects a false
equality boundary. A third selection retains the built-in `bool && bool`
node over both signed comparisons, lowers to kernel short-circuit evaluation,
and verifies the exact inclusive range offline. Its false upper-boundary
contract fails; `||` and non-Boolean `&&` remain outside the slice. A pointer fixture passes
`&value` from an `int&` caller to a mutable `int*` helper, then checks
dereference reads, a checked write, offline
verification, and expansion/reverification. Removing memory ownership and a
false memory postcondition both fail; pointer arithmetic, null conversion,
pointer locals, and multiple indirection are rejected at the frontend
boundary. A record fixture carries one aggregate struct's Clang declaration
identities and exact LP64 layout into the proof interface, then checks field
reads and writes plus a dereference through an `int*` field. It verifies
offline and after expansion; missing field authority and a false pointee effect
both fail. A local-aggregate fixture brace-initializes one object with every
field, lowers its exact layout to checked stack memory, and reads its fields
after initialization. It also verifies offline and after expansion; missing
input authority and a false saved-field result fail. Focused frontend checks
reject unresolved methods, bit-fields, inheritance, partial or default
initialization, copies, unsupported nested object forms, and unsupported local
lifetime combinations. Inventory regressions cover multiple distinct record
layouts and constant forests, shared lowering indexes, named resource budgets,
and malformed declaration graphs.
Destructor coverage additionally checks cleanup on every return, reverse order
for two top-level objects, and one direct nested block whose object is destroyed
both on early return and before an outer continuation. A sibling-block fixture
reuses one local spelling across two distinct non-overlapping lifetimes and
checks each block's early-return and fallthrough edges. An overlapping-lifetime
fixture checks one outer object plus one inner block object, including
inner-before-outer cleanup on early return, inner-only cleanup on block
fallthrough, and outer-only cleanup on the final return. A conditional fixture
checks that one object in one `if` arm is destroyed on that arm's early return
and fallthrough but is never constructed or destroyed on the skipped path.
Objects in both arms, conditional construction with another cleanup lifetime,
deeper nested blocks, shadowing while objects are live, and broader overlapping
forms remain focused frontend errors.
Other coverage exercises source/signature mismatch diagnostics, const-write
rejection, and smart-tactic inventory. Unsupported C++ does not fall back to
the C parser.

## What the gate runs

`scripts/check.sh` with no options is the single source of truth for "is this
tree green". It checks formatting (including the Rust exporter), environment
setup regressions, Clippy, the mdBook render, and docs lint; builds the C++ and
Rust exporters whose toolchains are installed; then runs the unit, API, documentation, and import tests in
parallel, followed by the mdtest and example harnesses one at a time, since
each of those verifies a whole corpus on every core.

### Frontend toolchains

C verification needs neither frontend toolchain. The C++ suites need LLVM and
Clang 19.1.7 for the exporter, and the Rust import tests need Charon's pinned
`rustc`. When `scripts/build-cpp-exporter.sh --check` or
`scripts/build-charon.sh --check` reports its toolchain missing,
`scripts/check.sh` skips the suites that need it and runs the rest. Without
the C++ toolchain it leaves out `tests/cpp_import.rs`,
`tests/bitcoin_core_money_range.rs`, `tests/libcxx_span.rs`, the four `click` command tests that run a
C++ mdtest (named in its filterset), and, through `CLICK_SKIP_CPP_FRONTEND`,
the C++ mdtests and examples. Without Charon it leaves out
`tests/rust_import.rs`. The gate names each skipped suite when it starts and
again after its elapsed time, so a partial run cannot pass for a full one.

CI and the nightly workflow build both toolchains and run every suite. Install
the toolchain before changing a frontend, or set `CLICK_REQUIRE_FRONTENDS=1`
to make a missing toolchain fail the local gate. An installed toolchain whose
build fails always fails the gate.

### The gate has a ten-minute budget

`scripts/check.sh` and a CI run each finish in under ten minutes on an
ordinary four-core machine. The script prints its elapsed time and warns past
the budget.

The budget is kept by what the gate leaves out, not by a faster machine:

- A test that takes half a second or more while the gate runs tests in
  parallel is marked `#[ignore = "nightly: <measurement>"]`. When that would
  leave a test file with no test in the gate, its fastest test stays. The gate
  kills a test still running after 30 seconds.
- A mutation test, which re-verifies a whole example with one C statement
  changed, is nightly. A family keeps at most one or two in the gate.
- An example that does is listed in `NIGHTLY` in `tests/examples.rs`, and an
  mdtest fixture that takes half a second or more is listed in `NIGHTLY` in
  `tests/mdtests.rs`. Shared `.click` lemma libraries stay in the gate.
  `MDTEST_FILTER` runs a nightly fixture by name.
- `click audit` re-expands and re-verifies every site of a claim, tens of
  seconds where `verify` takes under one. The import tests run it only under
  `CLICK_NIGHTLY`.
- The live Charon re-extraction is nightly.

`scripts/check.sh --nightly` runs all of it, with no budget, and
`.github/workflows/nightly.yml` runs that every night. It takes hours, so it
is not a per-PR check: agents and contributors do not run it before opening
or updating a PR. The gate is the merge bar; a nightly failure is fixed
forward. To check a change against nightly coverage it plausibly affects,
run those tests or fixtures by name (`MDTEST_FILTER`, `CLICK_EXAMPLE`, or one
`cargo nextest run --run-ignored all <name>`), and say in the PR what was not
run. The same workflow has a
second job, `scripts/check.sh --audit`, which runs `click audit` over the
whole repository on a release build: every smart tactic in the examples and
mdtests must expand to a proof that verifies. It takes about twenty minutes.
Before inventory, this entry point refreshes the native C import lock and
preprocessed sources for `examples/label-build-flags`, which are not checked
in. Rust examples retain their checked-in offline imports.
A proof container with a known audit failure is left out with `--exclude` in
that script, each beside the issue that tracks it; remove the exclusion with
the issue. `examples/basic-cpp` is also left out: its import lock and
compilation database are generated per machine by the test harness, so a
fresh checkout cannot load it, and `tests/cpp_import.rs` audits the C++ path.
When a new test would
push the gate past ten minutes, put it in the nightly gate; do not raise the
budget. Before 2026-10-06 the local gate had grown to 41 minutes and CI to 23
in five days, almost all from tool rechecks in the Rust import tests. By
2026-10-09 it had grown again to 30 minutes on four cores. 486 tests of two
seconds or more held about four fifths of its test time: Bitcoin Core money
range checks, rbtree erase mutations of a nightly example, Rust and C++
import checks, and `click audit` tests. They moved to nightly, leaving two
rbtree erase mutations in the gate. On 2026-10-13 the gate took 19 minutes on
four cores from a cold build, about 12 warm: the suites had grown sixfold
since August, and tests between half a second and two seconds held most of
the unit test time. The rule moved from two seconds to half a second, which
sent 672 tests, about 860 CPU-seconds of the 1,265 in the unit run, and 208
mdtests, about 340 of the corpus's 710, to nightly. A gate run without the
nightly fixtures is partial, as a CI partition is: the hidden prerequisite
ratchet checks only for a rise there, and the nightly run checks both
ratchets over the whole corpus.

CI uses these internal modes for code-affecting changes:

- `--ci-quality` runs formatting, setup regressions, Clippy, and documentation
  on its own runner, alongside preparation. It does not delay test runners.
- `--ci-prepare ARTIFACTS` builds both exporters and one archive containing
  all selected test binaries. It does not execute tests or quality checks.
- `--ci-shard ARTIFACTS SUITE [SHARD/TOTAL]` runs the selected archive tests
  without compiling Click or either exporter. Six deterministic nextest
  hash partitions cover the unit, C, and C++ import tests, and three more cover
  the Rust import tests, which alone need Charon; mdtests run on three
  runners, each taking every third file by `MDTEST_PARTITION`; examples run
  on two, by `EXAMPLE_PARTITION`. The build job saves its build snapshot only
  on a push to `master`, because every shard waits for that job to end. The build job takes about six of the ten minutes, so a shard has to
  finish in under four.

- Canonical examples that select native Charon imports load their locked
  artifacts in the ordinary example suite, without starting a compiler. Other
  compiler-backed examples keep their refresh checks. The nightly gate
  supplies fresh extraction coverage for native Rust examples.
- The live Charon tests re-extract Rust checkpoints and the complete
  fixed fixture parity inventory with pinned Charon and rustc, then checks
  every canonical contract through the shared verification engine. Replaced
  legacy sidecars have archived paths and SHA-256 digests in the inventory;
  the gate checks their recorded frozen outcomes independently. These ignored tests
  run in the nightly gate. `scripts/check.sh --charon-live` runs them alone,
  building pinned Charon first.

A push to `master` runs the build job alone, to save the build snapshot that
pull requests and the merge queue restore. The merge queue already ran the
whole gate on that exact tree, and repeating it after every merge took a dozen
runners that gating runs then waited for.

The final required `test` check requires quality, preparation, and every
partition to pass. A failed or cancelled quality job fails this gate even
when every test succeeds.

`scripts/setup-environment.sh` installs pinned nextest release binaries and
reuses matching installed versions, including source builds without commit
metadata. On Ubuntu 24.04 it caches the pinned LLVM package files; fresh
runners restore those files instead of reinstalling Clang. Native Rust
extraction uses the compiler/runtime identity in
`src/languages/rust/charon-profile.json`; `scripts/charon-toolchain.sh` derives
its runtime paths from that profile. Preparation bundles `rustc` and its runtime
libraries using `scripts/charon-runtime.sh` and both Charon executables in
`charon.tar.gz`, as a second artifact, `rust-toolchain`, apart from the test
binaries: together they are nearly half of the build output, and only the Rust
import tests start the compiler. The `rust` shards download that artifact,
validate the compiler, target, and toolchain identity, and restore those
libraries before setup, so missing caches do not prevent test execution; every
other shard downloads the test binaries alone. No shard installs another
compiler or mdBook. Preparation installs the pinned compiler with `rustc-dev`
and `rust-src`, builds Charon once, and archives it. The compiled-in profile owns extractor
pins, flags, and versioned adapter interpretations; the build script reads the
same profile. Cargo's extractor dependency pin is checked against it.

The build job caches dependencies, Click's own build artifacts, and
incremental compilation state under the compiler and dependency identity.
Each revision saves a new snapshot and later runs restore the latest
compatible snapshot. Cargo still checks source freshness and rebuilds changed
code. The quality job uses its own dependency cache. Build snapshots can be
large, so cache transfer and fresh-checkout rebuild costs must be included
when comparing CI timings; a cold cache still builds everything normally.

GitHub checks out the same source revision at the same absolute path on every
runner, preserving fixture and exporter sysroot paths embedded at compile
time. Test archives are extracted at the checkout root for embedded CLI
paths. Temporary upload archives stay outside the build cache.

For docs-only changes, CI and the explicit
`scripts/check.sh --docs-only` path run only the focused documentation gate
described above. The proof fixtures verify their inputs on every core. Judge
the verdict from the script's exit status.

The mdtest harness checks each `mdtests/*.click` file as an entry module as
well as each Markdown fixture. An import exposes a library theorem's statement
to a fixture; selecting the library itself checks its proof body. Keep shared
lemma files in `mdtests/` so the full gate checks both sides of that boundary.

The tree is clippy-clean, so a new diagnostic belongs to the change that
introduced it. When a lint is wrong about a deliberate design, silence exactly
that case with an `#[allow(clippy::…)]` carrying a one-line reason rather than
reshaping verifier behaviour to satisfy the lint. The crate-wide exceptions
live at the top of `src/lib.rs` with their reasons.

## Time-Bounded runs

Ordinary development and test builds carry no debug information
(`debug = false`): every test executable statically links all of Click, and
line tables alone made each one about 60% larger. A cold build of the gate's
test targets takes about 5.3 GB and 193 seconds on four cores, against 7.7 GB
and 243 seconds with line tables. This does not change optimization,
assertions, overflow checks, or incremental compilation. Panic and assertion
messages still give their file and line, and backtraces still name every
function. For file and line numbers in backtraces, rebuild with
`CARGO_PROFILE_DEV_DEBUG=line-tables-only
CARGO_PROFILE_TEST_DEBUG=line-tables-only`; for full variable and type
inspection in a debugger, use `2` instead. The dedicated `profiling` profile
continues to retain full debug information. Existing build artifacts do not
shrink automatically; clean an old target directory only when no task is using
it.

A machine that runs the gate once, such as a fresh cloud container, gains
nothing from Cargo's incremental cache, which is about 3.4 GB for the gate's
targets. `CARGO_INCREMENTAL=0 scripts/check.sh` skips it, and also makes the
cold build faster because there is no cache to write. Keep the default when
editing and rerunning: without the cache, a one-line edit recompiles all of
Click instead of taking about half a minute.

Prover regressions usually manifest as hangs rather than failures, so the
suite has a hard per-test time budget enforced by cargo-nextest. Prepare all
prerequisites for the full gate once per machine with
`scripts/setup-environment.sh`. For prose and documentation metadata changes,
use `scripts/setup-environment.sh --docs-only` to skip the LLVM packages used
only by the full gate. The setup script installs the Rust toolchain pinned in
`rust-toolchain.toml`, cargo-nextest, the pinned mdBook, and (on Ubuntu 24.04)
the pinned LLVM development packages. `scripts/check.sh` only looks tools up
and never reaches the network. Then run:

```sh
cargo nextest run
```

`.config/nextest.toml` reports any test slower than 10 seconds as slow and
kills a gate test still running after 30 seconds. No proof verdict depends on
wall clock; the kill decides only that a test is too slow for the gate. It
sits 60 times above the half-second rule because a 60-second per-test kill once
failed the 512-deep command-line boundary tests at random whenever other
builds loaded the machine. The nightly profile kills only after two hours, as
crash containment. Treat a slow report as a finding: split the test, move it
to nightly, or fix the prover slowdown it is exposing, and pin superlinear
work with a deterministic scaling regression. The
mdtest and example-project harnesses are aggregate tests covering many directly
verified fixtures, so their outer test-process allowance is not a per-project
verification budget.

Plain `cargo test` does not apply nextest's outer Rust-test deadline, which
is why `scripts/check.sh` refuses to run without nextest rather than falling
back to it. The fixture harnesses deliberately have no wall-clock proof
limit: deterministic tactic-work budgets decide their verdicts. Under
nextest, the aggregate mdtest and example test processes retain a 20-minute
outer timeout as crash/hang containment. The gate runs the two harnesses
with their output uncaptured, and each fixture prints a line when it starts
and when it finishes with its elapsed time, so a stall is visible as a
started fixture that never finishes, with its name, and a slow fixture is
visible while it runs rather than only in the total afterwards. A nextest timeout is therefore a tooling failure, visibly distinct
from the verifier's deterministic-budget diagnostic, and is not evidence that
a particular proof is invalid or too expensive. On 2026-08-20 the complete
mdtest and example harnesses took 58.2 and 17.6 seconds respectively, so the
20-minute containment boundary has more than 20x headroom over the slower
aggregate gate.

Every verdict, in the gate and in the shipped tools alike, comes from
deterministic work budgets; no tactic has a wall-clock limit. There is one
work counter: every unit the verifier records (`record_deterministic_work`,
and the cooperative checkpoints, which record through the same path)
charges the innermost active tactic's budget, every whole-run budget, and
every enclosing scaling measurement alike, so a step's cost in a scaling
regression is exactly what its budget is charged, and the same source spends
the same units on any machine under any load. A record does not interrupt
its caller; exhaustion leaves a pending limit that the next checkpoint
reports, and the verifier checks after every function, so a tactic cannot
finish green past its budget. Nested tactics charge their own budgets, not
their control parent's. A tactic-budget exhaustion names the tactic, its
class, its units, and the open and completed operation spans its units went
to when operation measurement is on (`click profile`, `CLICK_TIMINGS=1`).
Completed tactic events report both real CPU time and deterministic work, so
`click profile` keeps measuring actual latency without making that
measurement a correctness oracle.

Written pure-theorem tactics use these same scopes, including generic proofs,
structural induction, and nested `have` bodies. Their events retain the written
source path. A completed theorem ensure is a proof claim; its checking outside
tactics counts as verifier core rather than environment setup or C contract
certification. Nested tactic time remains exclusive.

The budgets are:

- the per-class tactic budgets, `TacticWorkLimits::default` (below);
- the whole-run budget of one `click verify` or `click profile` target
  (`click::cli::DEFAULT_VERIFY_WORK_LIMIT`, `--work-limit`) and of one
  `click expand` (`DEFAULT_EXPANSION_WORK_LIMIT`), installed by
  `click::cli::with_run_limits`, which also counts driver, certification,
  and lowering work outside any tactic; and
- `click audit`'s per-phase budgets.

Wall clock survives in two roles only. It is reported information: profile
timings and the reporting thresholds (`DEFAULT_SIMPLE_TACTIC_LIMIT` and its
siblings), which flag slow steps as findings but never fail a proof. And it
is crash containment: each tool's `--time-limit` (default
`click::cli::CRASH_CONTAINMENT_TIME_LIMIT`, ten minutes) stops a genuinely
hung or CPU-starved process, and the message of a run it stops says that it
was the crash-containment bound and not a verdict about the proof. The
`wall_clock_bounds_are_crash_containment_only` test in
`tests/documentation.rs` checks that no shipped source outside
`with_run_limits` installs a deadline. Until 2026-09-26 the shipped tools
also gave each tactic a real-time limit (500 ms simple, 2 s smart, 6 s
control, later 5 s simple) and each `click verify` sidecar a 30-second
deadline, so a proof could pass on an idle machine and fail under load:
`click audit examples/arena` failed at `arena_pipeline.contract` tactic 113
after 2.002 s against the smart limit.

Budgets are measured with one command:

```sh
scripts/measure-tactic-work.sh [REPORT_DIR]
```

It runs the mdtest and example harnesses with
`CLICK_DISABLE_TACTIC_BUDGETS=1`, so no cost is clipped (the harnesses' own
pinned budgets step aside too), and with `CLICK_TACTIC_WORK_REPORT` set, so
each fixture records in process the work every tactic charged and writes it
to REPORT_DIR (default: a fresh directory under `target/tactic-work/`). It
prints, per class and per corpus, the count, p50, p95, p99, second-largest,
and maximum, and the ten heaviest tactics of each class with their source
locations. Each fixture also records its whole verification as one `run`
row, which calibrates the whole-run budget. A fixture that fails with
budgets disabled is named, and its tactics are still measured.

The default budgets are 750,000 units for simple tactics, 2,000,000 for
smart tactics, and 2,500,000 for control tactics, calibrated on 2026-09-26
(base `a8ad65f7`) over 36 example sidecars and 2,354 mdtests. Simple: 9,161
tactics, p95 = 1,540, p99 = 4,847, max = 73,463. Smart: 12,200 tactics, p95
= 3,162, p99 = 21,899, max = 1,069,444. Control: 1,850 tactics, p95 = 4,864,
p99 = 17,831, max = 288,302. Every simple tactic is at least 10x under its
budget, so the simple budget stays the detector for a pathological simple
tactic; control has 8.7x. Smart has 1.87x, down from 3.0x the day before:
the arena proofs' heaviest `have` grew from 450,033 to 957,192 units. The
budget is not raised to regain headroom; that growth is a finding to reduce,
and surfacing it is the budget's job. It was reduced: the growth came from
`5815f41f8`, whose rewrite chain gave every remaining equality the whole
typed simp closure as a closing probe, and much of that closure's cost was
uncharged premise surface synthesis. The probe now asks the direct logical
closer, and the synthesis is lazy and charged, so the heaviest arena `have`
(`click profile`, after this calibration) is 488,691 units with every unit
counted, and the heaviest smart tactic is the failing mdtest `simp`
(1,040,194). The smart tactics near it are named
in `TacticWorkLimits::default` (an mdtest `simp` and the arena proofs' heavy
`have`s); they are slow steps to reduce, not headroom. The same run's `run`
rows calibrate the whole-run budget: the largest whole verification is
`examples/arena/arena_cells.click` at 6,536,557 units, so
`DEFAULT_VERIFY_WORK_LIMIT`'s 50,000,000 leaves 7.6x. Recalibration must run
the script over both the examples and the mdtests and record its statistics
there. Changing a work budget requires corpus measurements and a documented
reason; it is not a way to make one difficult proof pass.

### Adding a fixture harness

Every integration test file that reaches verification or expansion — the
mdtest, example, compiler-import, C++-import, and Bitcoin Core harnesses —
judges fixtures by the deterministic work budgets that every library
verification entry point installs, so a harness needs no special scope for
deterministic verdicts. It must not install a wall-clock bound of its own;
nextest's per-test timeout is the harnesses' hang containment, and
`wall_clock_bounds_are_crash_containment_only` in `tests/documentation.rs`
rejects a harness that calls `with_deadline`.

A harness that verifies on threads of its own declares
`#[path = "support/limits.rs"] mod limits;` and starts them with
`limits::spawn`, which gives each a 64 MiB stack, or fans fixtures out with
`limits::run_parallel`. Pinned per-fixture budgets, such as the mdtest
canaries, nest inside with `instrumentation::with_tactic_work_limits`. Add
the new harness to the fixture phase of `scripts/check.sh` as well.

### Command-line tests

The tests under `src/bin/` drive `click verify`, `expand`, `profile`, and
`audit` in-process with the tools' own limits: deterministic work budgets
decide, and the ten-minute crash-containment bound cannot fire for a test
the budgets accept, so machine load cannot change a command-line test's
verdict. Before 2026-09-26 the tools installed real-time limits (a 30-second
`verify` deadline, per-tactic clocks), each such test ran inside a
`with_work_budget_verdicts` scope that removed them, and under load the
512-deep expression-boundary tests once exhausted the deadline in the
environment phase and failed at random. The scope is gone because
production now behaves the way it did.

A test that shortens the wall-clock bound itself, with `--time-limit` or
`instrumentation::with_deadline`, is about crash containment, or only parses
the option; it goes on the short list of
`command_line_tests_name_every_wall_clock_bound_they_set` in
`tests/documentation.rs` with its reason. A test about a budget verdict uses
`--work-limit` or `instrumentation::with_run_work_limit` instead, which is
deterministic.

### Scaling regressions

The built-in standard library is parsed and resource-expanded once per process.
Only immutable surface declarations are shared; each verification constructs
its own environments and kernel session. The initialization-count regression
checks 1, 2, 4, and 8 fixture threads, including successful and failing programs
with conflicting declaration names. Keep this reuse across fresh mdtest threads;
a thread-local cache would repeat setup for every fixture.

An optimization that changes a hot-path representation or algorithm should
include a generated deterministic-work regression at four or more input sizes.
Test independent dimensions rather than one realistic example: functions,
straight-line statements, facts, surface spellings, resources, theorems, and
claims. Exclude fixed parsing/startup work where practical and assert the
growth ratio, not an elapsed-time threshold.

The intended bound for simple verification is output-sensitive `N log N` or
better. A benchmark that merely stays below the production deadline can still
hide quadratic growth and is not sufficient. Conversely, explicitly emitted
paths, quantified instances, premises, and definition members count as input
or output and may be charged accordingly.

Kernel memory snapshots have such regressions in
`src/kernel/tests/memory_scaling_tests.rs`: sequential stores into one block,
one store beside a growing number of unrelated cells, interning a one-store
derivative of an interned snapshot, and deduplication of equal content reached
by different routes. The same file bounds by a constant plus a logarithm the
work of one C store, one call havoc and its checker, one free, and one typed
load into a heap block beside a growing number of unrelated live allocations,
and re-deriving one store from the same base (a statement planned and then
checked) beside a growing number of unrelated cells, which must also hand back
the first derivation's storage. Normalizing allocation tokens in distinct heap
blocks must stay linear in the tokens.

Resource-context validity has its own in
`src/kernel/tests/resource_scaling_tests.rs`. Validity of a caller frame, and
composing one ensured range into it (a verified call's return), must cost
work that does not grow with unrelated owned allocations and instances beside
the target, nor with unrelated pointer equalities in the assumptions: the
check reads only indexed candidates (identities held twice or with invalid
access, blocks owning two or more ranges, and aliased bases, driven from the
smaller of the bases and the equalities). A companion test finds each
violation kind beside many unrelated resources from either side of the alias
walk.

End to end, `roundtrip_extra_copy_stays_nearly_flat_beside_unrelated_allocations`
in `src/surface/tests/scaling_tests.rs` verifies the frozen byte-representation
round trip beside 2, 4, 8, and 16 unrelated live heap allocations, with and
without one extra fixed `memcpy`, and bounds the extra copy's marginal work by
an eighth above its smallest value. It guards the collapse of the quadratic
fact comparison at every free and of the whole-context resource validity
sweep at every call; it is not the logarithmic contract, which the smart
`execute` planner does not yet meet (its test comment names the remaining
linear terms).

The contract is measured on the same family under explicit simple tactics.
`expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations`
expands both variants' smart proofs outside the measurement, at 1, 2, 4, and
7 unrelated allocations (seven is the largest member whose null-check chain
fits the checked drivers' nesting bound of eleven), and bounds the extra
copy's marginal verification work by its smallest value plus four units per
doubling. `expanded_roundtrip_work_per_source_byte_is_logarithmic` bounds the
whole expanded proof's work per C source byte, which is quadratic in the
allocations, by its smallest value plus one unit per doubling of the source.
`grouped_proof_finalization_reads_each_path_once` grows the early returns of
one function under a grouped proof and requires the implicit empty-effect
check to stay near-linear in the paths: a grouped proof issues one theorem per
path over one shared execution, and finalization visits that execution once.

Rust library tests and every fixture harness under `tests/` enforce the same
deterministic tactic-work budgets production does; neither has a wall-clock
tactic limit. Tests specifically about crash containment install an explicit
`with_deadline`. Fixture traversal runs on
every core and reports every failing fixture, while nextest owns the narrow
process-level timeout for an uncooperative hang. The former load-sensitive bubble-sort canary is pinned
at 100,000 deterministic units per tactic class; its measured maxima on
2026-08-20 were 146 simple, 21,090 smart, and 42,169 control units. The gates
do not rerun a successful proof to decide whether a noisy timing observation was
"confirmed": host throughput cannot change the semantic result in the first
place.

Reported tactic timings use per-thread CPU time on Unix, so descheduling is
not charged to a tactic's reported time. On platforms without a thread CPU
clock they fall back to wall-clock time. The crash-containment bound is
always wall clock. `CLICK_DISABLE_TACTIC_BUDGETS=1` remains a narrow A/B
diagnostic escape hatch; it must not be used for the ordinary correctness
gate.

### The key benchmark

`evals/speed.sh` is Click's headline performance number: nonblank
`.click` lines verified per CPU second over a small fixed set of examples,
"Click verifies the key benchmark at N lines/s". It is the number to move
when optimizing for general speed, and the one to report before and after a
performance change. Scaling regressions say whether a cost grows with the
wrong input; this says how fast ordinary proofs go.

The members are `arena` (call-heavy resource and ownership proofs, mostly
explicit steps), `rbtree-insert` (pointer-structure proofs), and
`owned-vector` (loops and owned buffers). They are a fixed list rather than
every example so that adding an example does not move the number; change
the list deliberately, to make it more representative, and re-baseline when
it or a member's proof changes substantially. `rbtree-erase` is measured as a
stress member and printed beside the headline but kept out of it: it is
three fifths of the corpus's verification time at about a third of the
speed, and would make the headline a measurement of one outlier.

Each member is verified with the optimized `profiling` build, fastest of
three runs, and its time is user plus system CPU time: verification is
single-threaded, and CPU time is far less noisy than wall time. `--work`
also reports deterministic work units per line through the example harness;
work is identical on any machine, so it is the figure to compare across
machines, while lines per second is the figure a user feels.

On 2026-10-12 at `0d2b58555`, on a 4-core cloud x86 machine, the key
benchmark verified 9,796 lines in 19.98 s of CPU, 490 lines/s (`arena` 570,
`rbtree-insert` 437, `owned-vector` 369); `rbtree-erase` ran at 159 lines/s.
With `--work` the key benchmark charged 15,059,650 units, 1,537 units per
line (`arena` 1,382, `rbtree-insert` 1,456, `owned-vector` 2,434;
`rbtree-erase` 4,755).

`evals/speed-survey.sh` remains the whole-corpus survey: every
example, wall time, so its number moves with the corpus.

### The `auto` eval

`evals/auto.py` measures, for a sample of the hand-written `have`
statements in the examples, how many `auto` proves where they stand and how
many can be deleted with the proof still verifying, against a committed
baseline. A change to `auto`, `simp` or what they rely on quotes its result,
sites gained and lost, in the pull request. `evals/README.md`
describes the corpus, the sampling and the baseline.

### Hunting for steps that grow

The key benchmark measures ordinary proofs; it cannot show a program that
makes `step` slow, because no member is such a program. A simple step must
cost work proportional to the statement it checks
(`docs/internals/verification-efficiency.md`), and a step has no expansion to
fall back on, so a C shape that makes one grow is a function Click cannot
check at the cost of its lines. `scripts/step-scaling-hunt.py` looks for
them: each shape generates a natural C function with an explicit
one-`step()`-per-statement proof at sizes 1 to 128 (more calls, more owned
parameter objects, more stated aliases, longer order-fact chains, deeper
pointer chains, longer increment chains, more sequential branches and loops,
more constant-index stores, more callees, more unrelated facts, more live heap
objects), verifies it, and reports each size's largest step in work units,
its mean step time, and its largest `loop` or `branch` clause. A shape whose steps stay flat in both is fine.
One that grows is filed in `bugs/` with the shape as its reproduction, and
its fix lands with an ordinary multi-size regression. A step whose own input
grows, such as one statement summing N fields or a `return` that releases N
locals, grows linearly by design; read the per-size output before filing.

Time is reported beside work because work counts only what is charged. The
hunt's first finding was invisible to it: an atomic proposition hashed its
debug text, which printed every memory snapshot it named, so each call in a
long function paid more than the last while every step charged the same work
(`hashing_a_memory_fact_is_constant_in_the_memory_size`).

### Surface throughput measurements

Deterministic work curves remain the correctness authority, but they do not
say whether the verifier's constant factor is pleasant for a user. Measure
surface throughput separately with an optimized `click verify` build, warm
filesystem caches, and the physical lines of the selected C and Click sources.
State the corpus, machine, worker count, and whether elapsed wall time or CPU
time is being reported. Do not combine compiler build time with verification
time or use profiler runs as the ordinary-command latency measurement.

On 2026-08-30 at `e988b120`, an 8-core Apple M3 MacBook Air verified the 19
example projects, selecting 6,866 physical C and Click lines. A temporary build
forcing the only optional invariant-path worker pool to one worker completed in
12.88--15.59 seconds, or about 440--530 lines per wall-clock second. Ordinary
optimized warm runs took 14.74--14.98 seconds, about 460 lines per second; their
user CPU time was 12.89--13.02 seconds, confirming that this corpus is
effectively single-threaded. Across nontrivial individual projects, proof
density produced roughly 250--1,700 lines per second. About 500 lines per second
is therefore a reasonable planning estimate for this corpus, not a
hardware-independent SLA or a substitute for multi-size scaling tests.

This snapshot also gives a concrete interpretation to an aspirational target:
10,000 selected lines in three seconds is about 3,300 lines per second, roughly
six to seven times this corpus-wide baseline. Re-measure after substantial
checker or corpus changes instead of treating the dated numbers as permanent.

The direct CLI is itself the bounding mechanism: `click verify --time-limit`
cooperatively interrupts execution, proposition derivation, memory resolution,
and resource search. Do not wrap Click in an external timeout command; a proof
search that outlives the CLI limit is a Click tooling bug.

## Artifact reuse rejection ratchet

Ordinary verification completes a proof's retained traces into the checked
function execution without executing the C body again. Where
opaque-contract certification cannot reuse a checked artifact, the contract
fails with the blocking premise kind or entry-state component and the
reason is counted (`instrumentation::ArtifactReuseRejection`; every pin is zero).
The fixture harnesses take that census after an unfiltered run and compare
it with the pinned baselines at the top of `tests/mdtests.rs` and
`tests/examples.rs`.

The comparison is exact in both directions. A count that rose means an
artifact that used to be reused no longer is, and that change must not
land. A count that fell means a rejection cause was removed; lower the pin in
the same change so the count cannot rise back. A filtered run
(`MDTEST_FILTER`, `CLICK_EXAMPLE`) or a run with `CLICK_RUN_QUARANTINED=1`
skips the comparison.

## Hidden prerequisite ratchet

A simple tactic must close each requirement by an exact or indexed check
([`issues/simplify-step.md`](https://github.com/clicklang/click/blob/master/issues/simplify-step.md)).
A `step()` no longer searches; where statement checking under the contextual
or explicit policies still derives a prerequisite by a search whose result
the proof does not retain, it counts the derivation by route and top rule
(`instrumentation::HiddenPrerequisiteRoute`). Both pins are empty. The fixture harnesses take
that census after an unfiltered run and compare it with
`HIDDEN_PREREQUISITE_BASELINE` in `tests/mdtests.rs` and `tests/examples.rs`,
exactly as the artifact reuse ratchet does: a count that rose must not land,
and a count that fell lowers its pin in the same change. A partitioned CI
shard (`MDTEST_PARTITION`, `EXAMPLE_PARTITION`) sees part of the corpus, so it
fails only when its own count exceeds a whole-corpus pin; an unpartitioned
run, such as a local `scripts/check.sh`, checks both directions. Library tests read
the same events per step through `collect_planning_statement_transitions`,
which records the claim and step of each hidden derivation.

## Quarantine

Known-broken and pathologically slow tests are quarantined so the default
suite is a meaningful green gate: any red is new signal, and nothing should
land red. Quarantine is always explicit and temporary — every entry names its
reason, and the goal is to shrink the list to zero, not to let it grow.

- Lib tests are quarantined with `#[ignore = "quarantined: ..."]` in the test
  source. Run them with `cargo test -- --ignored` or
  `cargo nextest run --run-ignored=only`.
- Mdtests are quarantined in the `QUARANTINED` list at the top of
  `tests/mdtests.rs`. Run one with `MDTEST_FILTER=<name>`, or all of them
  with `CLICK_RUN_QUARANTINED=1`.
- Example projects are quarantined in the `QUARANTINED` list at the top of
  `tests/examples.rs`. Run one with `CLICK_EXAMPLE=<name>`, or all of them
  with `CLICK_RUN_QUARANTINED=1`.

Before adding an entry, prefer fixing or reverting the offending change —
`git bisect` against a scratch worktree is cheap now that single tests are
fast to run. When a fix lands, remove the entry in the same change.

## Mdtests

Mdtests live in `mdtests/`. Each file can contain prose, one or more C blocks,
one Click block, and one expected result:

````text
```c filename=example.c
int32 example() {
    return 0;
}
```text

<!-- verified-example: mdtests/simple_tactics.md -->
```click
verifying "example.c";

int32 example() {
    ensures result == 0 by auto;
}
```text

```expect
pass
```text
````

Negative tests use an expected diagnostic substring:

```text
fail: expected diagnostic substring
```

### Termination is part of an mdtest's verdict

An mdtest is verified once, by the ordinary entry points, and termination is
part of what those check. A fixture whose summarized loop carries no
`decreases` clause, whose recursion carries no measure, or which calls a
`diverges` function without the marker is refused, and a fixture that expects
a pass must supply the evidence. There is no switch, no second run, and no
pending marker: a new mdtest is held to the rule from the day it is written.
`tests/examples.rs` and `tests/bitcoin_core_money_range.rs` hold example
sidecars and the one integration fixture to the same rule.

Use mdtests for focused language, lowering, proof, and diagnostic behavior.
For a focused C++ case, replace the C fence with exactly one C++ translation
unit and name the function selected for semantic import. For example, the
fence metadata can be `cpp filename=caller.cpp function=caller
profile=scalar_int32`; keep the usual Click and expected-result blocks.

`profile=normal_only` uses the exception-disabled baseline; `scalar_int32`
enables typed `int` throw/catch. The mdtest gate and the profile, expand, and
audit commands prepare the same locked C++ semantic import in a temporary
directory. Run `scripts/build-cpp-exporter.sh` first when using those commands
outside `scripts/check.sh`, or set `CLICK_CPP_EXPORTER` to the pinned exporter.
The C++ and C fences cannot be mixed in one mdtest. See
`mdtests/cpp_scalar_catch.md` for a real exception path.

## Example project tests

Example projects live under `examples/`. The integration test in
`tests/examples.rs` verifies `.click` sidecars against C files in each immediate
project directory.

Use example projects for larger library-shaped fixtures. Keep them small enough
that a reader can understand the proof boundary.

### Verifying one file or project directly

`click verify` is the plain verification command the expansion workflow ends
with. It takes either a sidecar or a directory:

```sh
click verify examples/input-cursor/input_cursor.click
click verify examples/input-cursor
click verify examples
```

A bare sidecar path verifies the proof units owned by that file. A
`:LINE:COLUMN` suffix verifies only the proof unit containing that one-based
source location. Imported theorem statements and unselected called-function
contracts are assumptions, not recursively selected proofs. This is the same
location scheme `click profile`, `click expand`, and `click audit` use, and the
targeted entry point the audit's cold reverification runs. A directory verifies
every sidecar in it: the directory
itself when it holds sidecars, otherwise each immediate subdirectory that does.
A declaration module (imports, types, predicates, pure functions, and
resources only) is checked through its importers and is not an entry
(`click::cli::project_sidecars`); the examples gate selects entries the same
way.
Every sidecar or selected proof unit has an independent deterministic
whole-run work budget (`--work-limit`, default 50 million units) and an
independent ten-minute crash-containment bound (`--time-limit`). Both cover
the whole run, from loading its sources on: source resolution and C parsing,
the external-dependency summary, and program-entry storage charge the budget
and stop at checkpoints like the proof phases do. The summary reads only
names, signatures, and call graphs; it builds no program-entry storage. An
exhausted budget exits unsuccessfully and names both the target and the
active tactic or open phases (`frontend > program-entry storage phase`);
one expensive project cannot consume the following projects'
budgets. A run the crash-containment bound stops says so, and that is not a
verdict about the proof.

That makes the expansion loop runnable end to end:

```sh
click verify path/to/file.click
click expand --in-place path/to/file.click:LINE:COLUMN
click verify path/to/file.click
```

When profiling attributes aggregate cost to a claim containing many individually
small smart tactics, expand the complete claim in one checked operation:

```sh
click expand --claim function.contract --in-place path/to/file.click
```

The first verification is a prerequisite, not merely a useful check:
expansion optimizes an already-correct selected proof unit. A failure later in
that proof blocks expansion of an earlier tactic. Repair the proof with
ordinary tactics first rather than moving between partially verified sources.
`click expand` then verifies the complete rewritten proof unit before it writes
anything. `--in-place` atomically replaces the source only on success;
`--output PATH` writes a checked sibling artifact without shell redirection.
Failures in unrelated proof units do not block this targeted workflow.

### Profiling slow proof steps

Start with `click verify`. If it reports a prompt correctness failure, repair
the proof before profiling it. Use `click profile` for optimization only after
verification succeeds. The exception is a target that times out or is
unexpectedly slow: profile it diagnostically to locate the incomplete work,
then restore successful verification before expanding anything.

Use `click profile` to find slow proof steps without letting one project run
indefinitely:

```sh
click profile examples
click profile mdtests/bubble_sort3_two_pass_sorted.md
click profile mdtests
```

Pass one sidecar, one example-project directory, the complete `examples`
directory, one markdown test, or a directory of them. Direct sidecar profiling
is useful for the sibling `.expanded.click` artifact printed by the expansion
workflow. An mdtest is profiled from its embedded
` ```c ` or ` ```cpp ` and ` ```click ` blocks using the same preparation the mdtests gate
uses, and reported locations point into the markdown file. Quarantine does not
apply — a quarantined mdtest is exactly the one worth profiling. The two modes
are told apart by shape: a directory that directly contains a markdown test is
an mdtests directory; otherwise example projects win whenever a Click sidecar is
found in or directly under the directory, so their `README.md` files are not
mistaken for mdtests. Project targets select sidecars exactly as `click verify`
does.

The defaults report smart tactics at 2 seconds, simple tactics at
500 milliseconds, control-tactic containers at 6 seconds, and stop each project
after 30 seconds. Override them with `--smart-threshold`,
`--simple-threshold`, `--control-threshold`, and `--time-limit`;
`--threshold` is shorthand for setting all three class thresholds equally.

The verifier emits each tactic's class as a structured event. The report uses
that class to prescribe the next action:

- Successful `SMART` hotspots in fully verified targets are expansion
  candidates. The report prints pasteable commands that write a sibling
  artifact, verify it, and reprofile that exact artifact with the same limits.
  Locked imports instead use `--in-place` and recheck the same sidecar, keeping
  its manifest and artifacts at their anchored name and location.
  A successful step observed before a later correctness failure or timeout is
  diagnostic only and produces no expansion command. Failed smart search has
  no successful proof; normally decompose the proof. An interrupted search is a
  tooling bug only when it ignores or badly overshoots its enforced bound.
- `SIMPLE` steps are deterministic checked operations. Do not expand them;
  reduce and fix the verifier bottleneck first.
- `CONTROL` steps are proof containers. Inspect their nested smart and simple
  timings rather than optimizing the container row by itself.

Intrinsic tactic class and selectable source-site kind are separate. `have`
is structurally a control container, but its complete selectable source site
is expandable automation for a supported smart body and a simple operation for
a nonempty all-simple body. Other `have` sites remain control containers. A
`loop` also remains intrinsically control when its keyword owns omitted phase
or effect automation. Timing renders the source-site kinds as SMART, SIMPLE,
and CONTROL; inventory and expansion use the same site-kind decision.

If a project reaches its limit, the report classifies every active step and
applies the same advice. This prevents slow legacy fallbacking from being
mistaken for smart search merely because it is nested inside a smart tactic.

The category sections list only steps that crossed a tail threshold. `TIME
ACCOUNTING` reconciles direct verification wall time across frontend,
environment, exclusive tactic classes, kernel certification, measured
`VERIFIER CORE` orchestration, and parent-observed `PROCESS/DRIVER` overhead.
`UNATTRIBUTED` is only the remaining inconsistent or unknown portion.

`WORK AND THROUGHPUT` counts completed simple leaves by kind, C transitions,
smart attempts and outcomes, functions, claims, and certification paths. It
reports aggregate rates and tactic averages/maxima. `DIAGNOSES` combines those
rates with the tail guards to distinguish SMART HOTSPOT, SIMPLE ENGINE BUG,
HEALTHY VOLUME, CERTIFICATION BOTTLENECK, SETUP BOTTLENECK, and UNEXPLAINED.
The displayed baselines are conservative development bounds, not a universal
hardware SLA.

A step whose timing names a tactic index the surface proof does not have keeps
its timing and loses only its location; those are listed under `STEPS WITHOUT A
SOURCE LOCATION`. Loop phases the verifier plans for itself index generated
tactics, so this is expected there.

The bounded report is intentionally a frontier rather than an exhaustive
profile beyond timed-out work. Fix simple bottlenecks before expanding one
smart location, then run the same command again. For raw function and tactic
timing, set `CLICK_TIMINGS=1`; add `CLICK_TIMING_STARTS=1` when an externally
interrupted run should identify its active statement. Raw tactic events include
`class simple`, `class smart`, or `class control`.

`NESTED VERIFIER OPERATIONS` lists the kernel operations measured inside
tactics and certification (resource context equality, relation facts,
proof completion, and so on) with their wall time and their deterministic
work units, aggregated by time and again by work. Work is what a tactic's
budget is enforced in and what a wall-clock profiler cannot see: an
operation that exhausts a budget in a few milliseconds ranks first by work
and nowhere by time. Read that table before adding ad hoc instrumentation.

### Profiling the verifier itself

`click profile` attributes time to proof steps and kernel operations. When the
question is where the verifier's own wall-clock time goes, which functions
rather than which tactics, record a sampling profile with samply:

```sh
scripts/profile-samply.sh examples/binary-tree
```

This builds the `profiling` cargo profile (optimized, with symbols) and opens
the recording in the Firefox Profiler; `--save-only` writes
`target/profiling/click.samply.json` instead. Install samply once with
`cargo install samply --locked`. A sampling profile answers "which function is
hot", never "which step exceeded its budget": those are different questions,
and the budget one belongs to `click profile`.

### Dependency-aware incremental verification

After a clean full verification, Click records a small atomic success marker
inside Git metadata for that exact commit, sidecar, and Click executable. It
records a marker only when the sidecar and its declared C sources match `HEAD`;
interrupted or dirty verification cannot attest a baseline.

Use the attested commit as a semantic comparison point:

```sh
click verify --changed-since HEAD~1 --explain examples/my-project
click verify --changed-since HEAD~1 examples/my-project
```

`--explain` is a dry run. The report lists selected functions, unchanged
functions whose baseline result is reused, and bounded reasons. Click compares
parsed C bodies, imported layouts, Click contracts, and proofs, so comments and
formatting do not invalidate results. A changed function selects its transitive
callers; the native verifier checks that set and its callees in one transaction.
Changes to shared predicates, pure functions, resources, or theorems select the
whole sidecar.

A different verifier executable (which includes its parser, kernel, proof
engine, builtins, and embedded standard library), a missing or corrupt marker,
an absent baseline source, and cache-schema drift all fall back to ordinary full
verification. The marker contains no theorem or proof object: it only attests
that the reference full gate passed. Full `click verify` remains the reference
release check.

### Expansion is not a repair operation

Expansion is deliberately not a repair operation for a broken proof. The
selected proof unit and the contracts it depends on must verify before `click
expand` will emit a rewrite. In particular, a failure later in the same proof
blocks expansion of an earlier tactic. First restore correctness with ordinary
proof steps; then profile and expand the green proof. Broken proof units must
not be moved between partially checked intermediate states under an expansion
label.

### Auditing smart-tactic expansion

Use `click audit` for a slow, exhaustive check of the source-expansion
boundary:

```sh
click audit examples
click audit mdtests
click audit .
```

The repository-root form is the complete manual expansion-boundary
gate: it covers examples and every passing mdtest in one resumable run.
Negative mdtests are excluded because their intended result is proof failure,
so they cannot supply successful expansions. The ordinary `cargo test` and
nextest gates keep fast unit, timing-parser, expansion, and markdown smoke
coverage; they do not run the exhaustive audit.

Kernel arithmetic axiom declarations are checked by verification but do not
contain an implicit smart proof, so they contribute no expansion-audit sites.

The audit first parses every proof container and builds a deterministic
inventory of smart source sites without executing any proof, printing its
size. Locations in mdtests use markdown coordinates, like `click profile` and
`click expand`:

```text
INVENTORY
  26 unique smart source sites
```

It then walks those unique `file:line:column` locations in path and source
order. A bounded verifier worker is started lazily when the cursor reaches a
sidecar or mdtest, so resuming in a later file does not initialize earlier
files. The resulting certified function environment stays alive while the
audit handles that file.

A claim whose sites are all selected is audited in one pass: the whole claim
is expanded once (`click expand --claim`), the expanded claim must hold no
smart tactic, and it gets the **verify** and **cold** checks below. Failure
of whole-claim expansion fails the audit. Expanding
one site runs its whole claim, so this costs a fixed number of runs of the
claim where the per-site path costs one per site. The per-site path that
follows is used only when `--start-at`, `--max-sites` or `--changed-since` selects a
claim in part. On that path each site gets the **expand**, **cold**, and
**reexpand** checks, and each claim gets one **verify** check covering all of
its sites:

1. **expand** — run expansion directly for that location,
   require the emitted proof container to differ from the on-disk original,
   and require it to round-trip through the ordinary Surface Click parser
   (there is no separate generated or Kernel Click grammar);
2. **verify** — once the claim's last selected site has been expanded, apply
   every site's rewrite to one copy of the proof and verify that in the
   retained session. The rewrites of one claim are disjoint edits of one
   proof, so the claim is verified once rather than once per site. Only when
   that combined proof fails, or two edits overlap, is each site's rewrite
   verified alone, which names the site whose rewrite fails. The session
   entry point additionally requires the location to resolve to the same proof
   unit as the baseline and the Click source to be identical outside that unit;
   it then reverifies just that proof unit while reusing certified dependencies.
   The retained session runs on a thread of its own: its certified environment
   names snapshots in that thread's kernel tables, which every other
   verification on a thread replaces, and a session refuses to reuse an
   environment whose tables were replaced;
3. **cold original/rewritten** — on the first site of each claim, directly
   verify the original and expanded versions of the same targeted proof unit
   without the retained session. Later sites explicitly report
   `cold comparison not run`;
4. **reexpand** — check that the rewrite is an expansion fixed point. The check
   is claim-based, because the rewrite moves and replaces tactics so the site
   cannot be re-found by its original position: the audited smart tactic must be
   gone from its claim's smart inventory and the emitted expansion must not
   have introduced a new smart tactic, so the claim's smart-site multiset
   strictly shrinks. A path-aligned certificate may remove multiple symmetric
   occurrences at once.

A passing audit prints one bounded row per claim by default:

```text
CLAIM [2/25] examples/owned-vector/vector.click  vector_copy.contract (1 sites) ... ok (1 sites)
```

Repeat `--claim LABEL` to select exact named proof units. Unknown labels are an
error; labels present in multiple sidecars are rejected as ambiguous unless the
audit target is narrowed to one sidecar or the claim is selected by location,
`--claim FILE:LINE[:COLUMN]`. `--verbose` prints all per-site phase
timings:

```text
[1/1] mdtests/scalar.md:16:47  scalar.arithmetic_result (auto) ... expanded (expand 1107 units, 25ms, cold original 1053 units, 13ms, cold rewritten 1240 units, 12ms, reexpand 163 units, 4ms)
CLAIM scalar.arithmetic_result verify 1 rewrite(s) ... ok (1210 units, 17ms)
```

### Small-stack canary

Checked verification advances a persistent `Proof`; its execution snapshot
(`ExecutionProofState`) is carried by value through the driver frames.
`selected_pure_case_split_simp_expands_by_removal` runs on an explicit 1.75
MiB thread stack, below libtest's 2 MiB default, and pins that representation
budget. The run needed between 1216 and 1280 KiB on rustc 1.92 / macOS and
overflowed a 1.25 MiB budget on CI's Linux toolchain, so the budget
carries about 40% headroom over the measured need; recalibrate on the CI
platform before tightening it. The outlined proof-rule and driver adapters
keep rule-local enum and proposition payloads out of their dispatchers'
frames; they are stable stack budget boundaries. Changes to those boundaries
must keep the small-stack canary green.

### Deterministic performance comparison

Audit's verdicts count deterministic work units, the units the tactic budgets
are charged (`click::instrumentation::measure_deterministic_work`), so the
same source reaches the same verdict on any machine under any load. Comparing
wall-clock time once let machine load fail a site. Raw site totals are
informational because all verification phases naturally grow with proof-unit
size. Audit compares the work of expanded cold verification with the
original's in the same run: the expanded proof fails when it spends both more
than twice the original's work and more than `--performance-slack` units
beyond it (default 10,000). One comparison decides, since a repeat spends the
same units. The failure reports both counts, the wall-clock times as
information, and commands that materialize and profile the exact expanded
artifact. `an_expansion_that_does_more_work_fails_the_comparison_deterministically`
and `an_audit_under_cpu_load_spends_the_same_work` pin both directions.

Each phase has a deterministic work budget: `--session-work-limit` (default
100 million units), `--expansion-work-limit` and `--verification-work-limit`
(default 50 million each). On 2026-09-26 the largest session measured was
`examples/arena`'s at 6.5 million units, and the largest expansion or
proof-unit verification under half a million. A process's first verification
also charges the one-time load of the built-in standard library, about 24,000
units; audit initializes its session before any comparison, so both compared
runs are warm.

A phase's wall-clock limit is crash containment only (default 10 minutes
each), for a hung or CPU-starved run. The whole run is also bounded by
`--time-limit` (default 10 minutes). Every blocking phase is capped by the
time remaining in that deadline, including session initialization and cold
verification. Reaching it stops at the current inclusive cursor, prints one
resume command, and exits unsuccessfully without counting deadline exhaustion
as a Click check failure.

### Time limits and resuming

| Option | Default | Bounds |
| --- | --- | --- |
| `--session-work-limit` | 100000000 | work of original-sidecar session initialization |
| `--expansion-work-limit` | 50000000 | work of one expansion, and of the re-expansion check |
| `--verification-work-limit` | 50000000 | work of one retained or cold proof-unit verification |
| `--performance-slack` | 10000 | minimum expanded-over-original work increase, beside the 2x ratio |
| `--session-time-limit` | 10m | crash containment for session initialization |
| `--expansion-time-limit` | 10m | crash containment for one expansion or re-expansion |
| `--verification-time-limit` | 10m | crash containment for one proof-unit verification |
| `--time-limit` | 10m | the whole run's wall clock |

`--claim` and `--verbose` are selection/presentation controls and are retained
in resume commands; they do not weaken any selected site's checks.

Use `--changed-since REVISION` to audit only smart-tactic claims affected by a
Git change. It uses the same parsed C/Click comparison and reverse-call
dependency selection as incremental verification. A changed function selects
its claims and callers' claims; shared predicates, resources, pure functions,
or theorems select the whole sidecar. A missing or unparsable baseline also
selects the whole sidecar. When auditing Click's own checkout, changes to its
parser, kernel, verifier, standard library, CLI, or build inputs select the
complete audit. `--claim` intersects with this semantic selection, and both
options are retained in resume commands.

`--discovery-time-limit` remains as a compatibility alias for
`--session-time-limit`; `--slow-site-limit` is a compatibility alias for
`--performance-slack`.

By default the audit stops at the first session, expansion, verification,
fixed-point, work-budget, or performance failure and prints a copy-pasteable
continuation command carrying every current limit:

```sh
click audit --session-work-limit 100000000 --expansion-work-limit 50000000 \
  --verification-work-limit 50000000 --performance-slack 10000 \
  --session-time-limit 10m --expansion-time-limit 10m \
  --verification-time-limit 10m --time-limit 10m \
  --start-at path/to/file.click:LINE:COLUMN examples
```

`--start-at` is inclusive, so fixing a failure and running the suggested
command retests that same site before continuing. The cursor also skips
session initialization for preceding files. `--keep-going` requests the older
failure-collecting behavior. Use `--max-sites` only for a deliberately partial
diagnostic run; it prints the next cursor when the bound is reached. A release
or expansion-boundary audit should omit it and finish one complete pass.

Every site starts from the unchanged baseline source, so an earlier rewrite
cannot hide or cause a later failure. With `--keep-going`, a failed session is
rebuilt from a fresh complete verification before the audit continues. The command exits
unsuccessfully if session initialization, expansion, parsing, source isolation,
proof-unit verification, the fixed-point check, a phase work budget, the relative
performance contract, or the run limit fails.

Proof scripts have no runtime semantics. Re-verifying the same isolated claim
is the semantic audit condition; requiring the automation and generated
explicit proof to visit byte-identical internal branch/path states would reject
valid expansions and is intentionally not an audit invariant.

## Unit tests

Rust unit tests are appropriate when the behavior is lower-level than a sidecar
can express clearly, such as parser details, kernel term simplification, or
specific reasoning helpers.

## Test selection

When adding a feature, prefer this order:

1. Add or update an mdtest that demonstrates the user-visible behavior.
2. Add unit tests for lower-level parser or kernel behavior if needed.
3. Add or update an example project only when the feature changes the shape of
   realistic verification.
4. Update the relevant docs.

Mdtests are the main executable documentation for Click's proof surface.
