# Testing Click

`tests/process_containment.rs` checks the CLI's independent crash watchdog.
The debug-only `CLICK_DEBUG_BLOCK_VERIFIER` hook parks the verifier after its
containment scope opens, without polling a deadline. The child must exit with
a containment message; an independent outer test bound kills a broken child.
A normal verification also checks cancellation of a long-lived watchdog.
Audit regressions distinguish its whole-run pacing deadline from a phase's
crash bound: a short healthy run prints a summary and resume command, while
a deliberately blocked phase retains its configured watchdog duration.
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
are in `bugs/README.md` and `roadmap/README.md`.

A smart tactic that promptly reports that it did not find a proof is not one of
these tooling failures. Smart search is heuristic and incomplete. Continue
with a smaller search or explicit relevant simple tactics, following the
[proof repair procedure](../concepts/tracing.md).
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

```console
scripts/check.sh
```

For a change limited to prose or documentation metadata, use the focused
documentation gate:

```console
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

Use a focused nextest run while iterating on one proof fixture or example.
These commands reuse the ordinary gate build and keep nextest's containment.
Replace the file or project name with the one affected by the change.

```console
MDTEST_FILTER=indexed_iterated_ownership.md cargo nextest run --lib --features fast-gate -E 'test(=gate_tests::mdtests::mdtests)'
CLICK_EXAMPLE=arena cargo nextest run --lib --features fast-gate -E 'test(=gate_tests::examples::example_projects)'
```

Explicit names also run fixtures assigned to nightly. CI runs the full gate
for code changes.

To run the default Markdown fixture suite on its own:

```console
cargo test --test mdtests
```

Standalone `.click` files in `mdtests/` are independently verified entry modules,
including helpers imported by other fixtures. The harness propagates both input
summary failures and verification refusals: a successful dependency summary alone does not
pass a fixture.

Run the larger example-project verifier with:

```console
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
`roadmap/kernel-scale-preprocessing.md` in the same change.

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
including those headers, before the network-free gate runs. Where the network
denies `apt.llvm.org`, as in Claude Code cloud sessions, it instead installs
the official LLVM 19.1.7 Linux x86-64 release with
`scripts/install-llvm-release.sh`. The archive must match its pinned SHA-256,
and only Clang, `llvm-config`, headers, and libraries are extracted, to
`/opt/LLVM-19.1.7-Linux-X64`. Ubuntu's packages supply GCC and the headers.
`/usr/lib/llvm-19` links to that directory, and setup accepts a pinned LLVM
there, not only `llvm-config-19` on `PATH`.

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
reuses one local name across two distinct non-overlapping lifetimes and
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
setup regressions, the mdBook render, and docs lint; builds the C++ and
Rust exporters whose toolchains are installed; then runs the unit, API, documentation, and import tests in
parallel, followed by the mdtest and example harnesses one at a time, since
each of those verifies a whole corpus on every core.
Production builds, Clippy and command-line tests run in `--nightly`.

### Frontend toolchains

C verification needs neither frontend toolchain. The C++ suites need LLVM and
Clang 19.1.7 for the exporter, and the Rust import tests need Charon's pinned
`rustc`. When `scripts/build-cpp-exporter.sh --check` or
`scripts/build-charon.sh --check` reports its toolchain missing,
`scripts/check.sh` skips the suites that need it and runs the rest. Without
the C++ toolchain it leaves out `tests/cpp_import.rs`,
`tests/bitcoin_core_money_range.rs`, `tests/libcxx_span.rs`,
`tests/libcxx_functional.rs` and the C++ mdtest import freshness check; the C++
mdtests and examples still run from their checked-in imports. Without Charon it leaves out
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

Before moving a slow regression out of the gate, try reducing its fixture.
Identify the behavior and threshold its assertions protect, retain the original
source pattern, and remove input beyond what exercises that threshold. Check
that the reduced test still fails when the original defect is restored, then
compare before/after timings on the same build and machine. Keep integration
controls and multi-size scaling coverage: a smaller fixture must preserve the
claim the test makes. For example, a trace-truncation regression needs just over
the old fact cap, while a storage-budget regression needs enough initialized
objects to exhaust the same budget in the same phase.

The budget is kept by what the gate leaves out, not by a faster machine:

- A test that takes half a second or more while the gate runs tests in
  parallel is marked `#[ignore = "nightly: <measurement>"]`. If the test
  belongs to a target compiled by the fast gate, also add
  `#[cfg(not(feature = "fast-gate"))]` so the gate build omits its body.
  When that would leave a test file with no test in the gate, its fastest
  test stays. The gate kills a test still running after 30 seconds.
  One approved exception: `standard_library_theorems_are_proved_by_their_own_entry_point`
  proves every library theorem through `verify_standard_library`, about 7.5
  CPU-seconds in a debug build, and stays in the gate as its only proof of the
  library.
- A mutation test, which re-verifies a whole example with one C statement
  changed, is nightly. A family keeps at most one or two in the gate.
- An example that does is listed in `NIGHTLY` in `tests/examples.rs`, and an
  mdtest fixture that takes half a second or more is listed in `NIGHTLY` in
  `tests/mdtests.rs`. Shared `.click` lemma libraries stay in the gate.
  `MDTEST_FILTER` runs a nightly fixture by name: a value ending in `.md`
  selects exactly that file, and any other value every file whose name
  contains it.
- `click audit` re-expands and re-verifies every site of a claim, tens of
  seconds where `verify` takes under one. The import tests run it only under
  `CLICK_NIGHTLY`.
- The live Charon re-extraction is nightly.

`scripts/check.sh --nightly` runs all of it, with no budget, and
`.github/workflows/nightly.yml` runs that every night. It takes hours, so it
is not a per-PR check: agents and contributors do not run it before opening
or updating a PR. The gate is the merge bar; a nightly failure is fixed
forward. To check a change against nightly coverage it plausibly affects,
run those tests or fixtures by name. Use `MDTEST_FILTER` or `CLICK_EXAMPLE`
for corpus entries. For a nightly-only Rust unit test, run
`cargo nextest run --lib --run-ignored only <name>` with the default feature
selection. For a nightly-only integration test, use its standalone
`--test <target>` in place of `--lib`. Say in the PR what was not run.

The nightly workflow runs four jobs in parallel:

| Job | Command | Checks |
|---|---|---|
| `slow-tests` | `scripts/check.sh --nightly` | production builds, Clippy, CLI behavior and the tests above |
| `expansion-audit` | `scripts/check.sh --audit expansion` | every smart tactic expands to a simple proof that verifies |
| `raise-lower-audit` | `scripts/check.sh --audit raise-lower` | every fact and goal round-trips through Surface |
| `fact-stability-audit` | `scripts/check.sh --audit fact-stability` | lowering never depends on facts |

The three audits are `click audit <audit>` over the whole repository, the
examples and the mdtests, on a release build (`scripts/audit.sh`,
[`click audit`](../reference/cli/audit.md)). Each ends with one headline:
how many of the items it checked fail. `scripts/check.sh --audit` alone runs
all three. The expansion audit takes about twenty minutes. Every example's
import lock and prepared artifacts are checked in, so the examples need no
compiler or front end; only the C++ mdtests use the pinned exporter.
A proof container with a known audit failure is left out with `--exclude` in
`scripts/check.sh`, each beside the issue that tracks it; remove the
exclusion with the issue.
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
ratchets over the whole corpus. On 2026-10-15 the warm local gate took 11.7
minutes on four cores, from one example: `examples/rbtree/rbtree-augmented` grew
from 259 to 5,467 proof lines in a day and verified in 261 seconds of the
examples harness's 317, so it joined the other rbtree examples in nightly.

### Nightly report

The nightly workflow's `report` job writes a short report of each run to the
`nightly-reports` branch, which shares no history with `master`, and to the
run's summary page. Read it with:

```console
git fetch origin nightly-reports && git show FETCH_HEAD:report.md
```

`report.md` lists each failing check with the first line of its diagnostic
and the command that reproduces it locally. Since the previous night's
report, it marks each failure new or persisting and lists the checks that
were fixed or did not run. It also groups failures that share a diagnostic
shape, times each phase, and names the slowest checks. `report.json` holds
the same data, and the branch history keeps every night's report. To see
what changed between two nights, diff the branch's commits.

The report is built from records the run leaves when
`CLICK_NIGHTLY_REPORT_DIR` is set: one JSON line per mdtest fixture, example
project, and failed `click audit` site (`src/nightly_report.rs`); nextest's
JUnit results for the nightly profile; and each `check.sh --nightly` phase's
time and exit status. `scripts/nightly-report.py` renders them, and
`scripts/test-nightly-report.py` exercises it in the gate. A job that fails
without recording a failing check, such as a build error or a timeout, is
reported as that job's failure, with the run log as its reference.

The `raise-lower-audit` and `fact-stability-audit` jobs record each lowering
audit of [the raise-lower principle](raise-lower-principle.md#the-raise-lower-principle)
as its headline numbers (`failing`, `checked`, `tracked`, `unexpected`) and
outcome counts. A fact-stability `differs` or `paths` lowering fails the
night, as does an audit run that does not complete. `unexpected` counts the
proof containers that did not verify as their expectation says; the gate and
the `slow-tests` job own those verdicts, and `<audit>.unexpected.tsv` lists
them. For each lowering audit, the report lists up to 20 failures that are
new since the previous night, each with the `click audit` command that
reproduces it; the audit job's artifact holds `<audit>.failures.tsv`, every
failure with its command. The raise/lower round trip is not enforced: the
report lists its counts beside the previous night's and flags a rise in any
count but `same` and `checked`.

## Gate timing baselines

The **gate timing baselines** are the reference for expected gate speed. When
asked to compare a run with the baselines, use this section and match the
environment, cache state, command, and source revision before interpreting a
difference. These observations are separate from the ten-minute gate budget;
first-time prerequisite installation is outside that budget.

Distinguish three scenarios:

1. **Fresh machine:** start with a supported OS and an empty checkout, tool,
   Cargo download, build, and incremental cache. Count prerequisite setup plus
   the first full gate. Exclude provisioning the VM or pulling its OS image.
2. **Edit and rerun:** retain tools, downloaded dependencies, and compiled
   dependencies; make a Rust change and run the full gate. Record the change
   and whether Click's own incremental state was retained: adding one test
   and rebuilding all of Click are different workloads.
3. **Unchanged rerun:** immediately repeat the full gate with the same source
   and build artifacts. This measures the test-execution floor, not editing
   performance.

All local measurements use plain `scripts/check.sh`, with both compiler
frontends installed and no test filters. These are single-run observations,
not medians or timing guarantees. Unknown cells mean unmeasured; do not
substitute the ten-minute target or a partial-cache measurement.

| Environment | Fresh setup + first gate | Edit and rerun | Unchanged rerun |
| --- | --- | --- | --- |
| Codex cloud, 4 CPU cores / 16 GiB, Linux x86-64 | 15m09s of commands: 6m01s setup + 9m08s gate | 5m25s for one added Rust test; 7m00s for a full Click rebuild | 4m50s |
| GitHub Actions, `ubuntu-24.04`, sharded workflow | Unmeasured with all Click caches empty | 6m11s with build and tool caches restored | 6m15s for a same-source merge-queue workflow |
| Claude Code cloud, 4 vCPUs / 15.7 GiB, Linux x86-64 | 24m19s of commands: 4m32s setup + 19m47s gate | 10m56s for one added Rust test; 17m13s for a full Click rebuild | 9m37s |

The CI unchanged case tests an identical Git tree in a new workflow, not the
same executable in the same working directory. It includes fresh checkouts,
remote cache restores, compilation as needed, artifact transfers, and runner
startup. Its few seconds of difference from the edited case are not evidence
that an unchanged source tree is slower. A fully cold CI measurement remains
missing; the 9m40s comparison below must not fill that cell.

The Claude Code cloud machine runs every phase about twice as long as Codex
cloud, not only edits. At `929f45018`, with no compilation in either run, its
unit/API tests took 1.97 times as long (248.61s against 126.50s) and its
fixture tests 2.00 times (306.87s against 153.29s); the same added test's
incremental build took 2.10 times (79s against 37.59s). Both machines run
four CPUs' worth of work and the tests use every core, so the ratio measures
per-core speed: a 2.1 GHz Intel Xeon VM against an AMD EPYC 9V45 host.
Steal time was under 1% of the session's CPU time. Compare a gate run with
the row for its own environment; a Claude Code cloud gate near ten minutes is
its unchanged floor, not a regression.

### Environment resource profile

The Codex cloud resource profile was inspected on **2026-10-24**. The fresh,
small-edit, and unchanged timings were measured on that date using verifier
commit **`929f45018944c9443be3b29199e091f27f7ae93e`**, plus the provisioning fixes
described below and the documented temporary test for the small-edit case.
The earlier full Click rebuild used that same verifier commit on **2026-10-23**.
The Claude Code cloud profile was inspected on **2026-10-24**, the date of
all its timings; the evidence below gives each timing's revision.

| Resource | Codex cloud measurement environment | Claude Code cloud measurement environment |
| --- | --- | --- |
| CPU allocation | **4 CPU cores of effective quota** (`cpu.max = 400000 100000`); CPU affinity exposes 5 logical CPUs | **4 vCPUs** of a KVM virtual machine, one thread per core; no cgroup CPU quota (`cpu.cfs_quota_us = -1`), affinity 0-3 |
| CPU model / architecture | AMD EPYC 9V45 96-Core Processor; `x86_64` | Intel Xeon Processor @ 2.10GHz (family 6, model 207); `x86_64` |
| Memory | **16 GiB** cgroup limit (`memory.max = 17179869184`), including the benchmark container; no configured swap | **15.7 GiB** VM memory (`MemTotal: 16477348 kB`), no memory cgroup limit; no configured swap |
| Storage | Approximately **31.5 GiB** shared ephemeral overlay filesystem, with about 16 GiB free before the fresh benchmark; Cargo and Docker used this same storage | Per-session writable allowance on a 252 GB virtual disk, with about 18 GiB free before the fresh benchmark; the gate's `target/` reached 5.9 GiB |
| Operating system | Host: Debian GNU/Linux 13.6, kernel 6.18.55; clean benchmark container: Ubuntu 24.04 | Ubuntu 24.04.5 VM, kernel 6.18.44; no nested container |
| Build concurrency | **5 Cargo jobs**; ordinary gate defaults for test and fixture workers; no competing benchmark builds | **4 Cargo jobs** (the default); ordinary gate defaults; no competing builds |
| Compiler/frontends | Rust and Cargo **1.98.1**; LLVM/Clang **19.1.7**; Charon's pinned **nightly-2026-09-17** Rust toolchain | Same versions |
| Test/docs tools | Clean benchmark: nextest **0.9.143**, mdBook **0.4.52**; the host's later documentation-validation check used nextest 0.9.146 | Clean benchmark: nextest **0.9.143**, mdBook **0.4.52** |

The nested benchmark container had the same four-core quota and 16 GiB limit;
it did not add resources to the host's allowance. The CPU model names the host
processor, not the number of cores allocated to this task. Compare effective
CPU and memory limits rather than host-wide totals reported by `/proc`.
The GitHub Actions samples use standard `ubuntu-24.04` hosted runners; their
logs do not establish an exact CPU model or memory allocation, so the cloud
resource values above must not be attributed to those runners. Their dates,
checked-out revisions, and workflow links are recorded below.

### Measurement evidence

- **Codex cloud fresh setup:** measured on 2026-10-24 at `929f45018`, with
  this change's provisioning fixes and no verifier changes. The host is Debian
  13; the isolated container is Ubuntu 24.04, with a four-core CPU quota,
  16 GiB memory limit, and five Cargo jobs. No host compiler, tool, Cargo, or
  build cache was mounted into it. The 6m01s setup sum includes base build tools,
  rustup, the pinned Rust and LLVM toolchains, nextest, mdBook, repository
  checkout, and failed setup attempts. The first plain gate then passed in
  9m08s, including exporter builds and all 6,476 unit/API tests and four corpus
  tests. The 15m09s total sums timed commands and excludes the agent's diagnostic
  pauses; it was not one uninterrupted setup invocation. Provisioning the OS
  image is also excluded.
- **Fresh-setup fixes:** the cloud network denied `get.nexte.st`, so the
  pinned nextest release was obtained from its official GitHub asset. Setup now
  falls back to that URL automatically. Ubuntu's minimal image also omitted
  manual files still listed by dpkg; the LLVM cache writer now skips missing
  documentation while preserving installed documentation and failing on
  missing compiler files. All setup attempts are counted above; no compiled
  artifacts were imported to recover from those failures.
- **Codex cloud unchanged run:** immediately following the fresh gate, using
  the same Ubuntu container, compiler artifacts, verifier, and corpus, the
  full gate passed in 4m50s. Nextest's cached build took 0.12s; unit/API tests
  took 126.50s and the four fixture tests took 153.29s.
- **Codex cloud small edit:** in that same container, with incremental state
  retained, appending one temporary unit test to `src/lib.rs` made the next
  full gate take 5m25s. The test asserts that `std::hint::black_box(2) + 2`
  equals 4; it changes no verifier logic or proof input. The incremental test
  build took 37.59s, and all 6,477 unit/API tests and four fixture tests passed.
  The temporary test is a benchmark edit, not part of the repository.
- **Codex cloud rebuild:** measured on 2026-10-23 at `929f45018` in
  [PR #1920](https://github.com/clicklang/click/pull/1920). Rust 1.98.1,
  five Cargo jobs, dependencies already compiled, Click rebuilt. The full gate
  passed in 7m00s; compiler-process RSS peaked at 8.48 GiB. This is a substantial
  rebuild observation, not a promise that every one-line edit takes seven
  minutes.
- **Claude Code cloud fresh setup:** measured on 2026-10-24 at `333383d71`,
  in a Claude Code on the web session. A separate worktree had its own empty
  `RUSTUP_HOME`, `CARGO_HOME`, `CLICK_TOOL_ROOT`, Cargo registry, and
  `target/`. The 4m32s setup sum is rustup 0.5s, Rust 1.98.1 12.4s, Charon's
  nightly toolchain 24.4s, nextest 0.9.143 from its GitHub release 1.0s,
  mdBook built by `scripts/install-tools.sh` 80.7s, and the official LLVM
  19.1.7 Linux x86-64 release tarball downloaded and unpacked (8.2 GiB) in
  152.9s. At that revision, `scripts/setup-environment.sh` could not complete
  there because the session network denies `apt.llvm.org`; setup now installs
  the same release, extracting 2.5 GiB of it, in 161s. The exporter was then
  built against the image's preinstalled `/usr/lib/llvm-19`, the same release;
  GCC came with the image. About 3s of benchmark-script errors are excluded. The first plain
  gate passed in 19m47s: Charon build 1m24s, test build including crate
  downloads 5m58s, 6,524 unit/API tests 316.06s, four fixture tests 340.41s.
- **Claude Code cloud rebuild, unchanged, and small edit:** measured on
  2026-10-24 in the same worktree at `929f45018`, starting from the
  `333383d71` build state. Only `clicklang` recompiled; the gate passed in
  17m13s with a 6m46s test build. The immediately repeated gate passed in
  9m37s: test build 0.17s, 6,476 unit/API tests 248.61s, four fixture tests
  306.87s. Appending the same temporary `black_box` test as the Codex small
  edit to `src/lib.rs` made the next gate take 10m56s, with a 79s incremental
  test build and 6,477 unit/API tests. At `333383d71`, the unchanged gate took
  10m06s, and appending one unused function to `src/kernel/spec.rs` took
  11m21s with a 56.92s incremental build.
- **GitHub Actions cached edit:** the successful
  [tests run for PR #1963](https://github.com/clicklang/click/actions/runs/40110835408)
  on 2026-10-24 took 6m11s from the first `scope` job log to the final `test`
  check, testing merge commit `9588023c0`. It restored tool caches and the
  compatible `master` build state.
  Preparation took 3m41s, including cache restore, exporter work, a 51.80s test
  build, and artifact upload. Shards and orchestration completed the remaining
  time. The interval excludes initial runner queue time but includes waits
  between jobs and artifact transfers.
- **GitHub Actions unchanged source:** the successful
  [merge-queue run for PR #1960](https://github.com/clicklang/click/actions/runs/40110304932)
  on 2026-10-24 took 6m15s by the same clock. Its checked-out commit
  `7c8dfce80` and the preceding PR run's checked-out merge commit `879f26cb5`
  both have Git tree `0ab69065245b88683a3c519f17edf64107f73ba1`.
  Tool caches hit and the build state came from `master` at `10cb3a2e7`.
  Preparation took 3m53s, including a 27.52s test build. This is a measured
  same-source workflow, rather than an assumption that a queue run has the
  same source as its PR run.
- **GitHub Actions Cargo-cold comparison:** the successful
  [tests run for PR #1920](https://github.com/clicklang/click/actions/runs/40022592662)
  on 2026-10-23 took 9m40s by the same clock. Its Cargo build-cache lookup
  missed, but LLVM, Charon compiler-runtime, nextest, and documentation-tool
  caches hit. This is **not** a fully fresh-machine measurement. Preparation
  took 7m12s, including a 3m50s test build and artifact upload.

### Updating the baselines

Pin one revision for a comparison. Record the OS, architecture, effective CPU
quota, memory limit, Rust/tool versions, Cargo job count, frontend availability,
source diff, exact commands, cache state, elapsed wall time, and exit status.
Keep measured results distinct from estimates. Do not measure competing builds
at the same time, silently omit unavailable frontends, increase stack or work
limits, or treat an interrupted or failing run as a passing baseline.

For a fresh measurement, isolate the checkout and all caches in a disposable
machine or container; do not clear another developer's working caches. Time
setup and the gate separately, then add them for the first-run total. Retain
those caches for the unchanged and edit measurements. For CI, inspect cache-hit
logs and the complete workflow interval; summing parallel job durations does
not measure how long a user waits. Record a fresh row only when tools as well
as Cargo artifacts were absent. A retry of CI still uses a new hosted runner
and can restore remote caches; it is not equivalent to a local unchanged run.

## One verifier build in the budgeted gate

The ordinary `scripts/check.sh` gate compiles only the library test target,
with `--lib --features fast-gate`. `src/gate_tests.rs` includes the existing
API and proof-fixture harnesses in that same `cfg(test)` executable. Tests
that launch the real `click` binary, including command dispatch and installation
checks, remain in their standalone targets for `scripts/check.sh --nightly`.
The nightly also compiles and lints the normal production configuration.
The fast gate is a test-configuration verdict; production/CLI coverage is a
nightly policy rather than an extra build on every edit.

`scripts/fast-gate-build.sh` uses the ordinary Rust compiler. Clippy runs with
production checks in nightly: its driver changes MIR optimization and compiler
checks for lint analysis, so its code generation is not used for executable
tests. The local script saves nextest's binary metadata and runs those binaries
without another Cargo build. CI archives that same test executable and
partitions it by test-module names.

One verifier target also prevents Cargo from compiling the production library
and its large unit-test variant at the same time. Dependencies still build in
parallel under the usual Cargo job limit. The remaining test compilation can
still need several GiB; this removes overlapping verifier builds rather than
placing a memory cap on rustc.

The unit/API group runs in parallel. The markdown harness and example-project
harness run separately, each using all available cores. Their existing work
budgets and nextest containment remain in force. `fast-gate` excludes executable-
dependent functions at compile time because those functions require the
normal application binary. It also excludes nightly-only Rust tests in the
shared harnesses and library unit modules. The default-feature targets retain
those tests for nightly. Fast-only support modules deliberately
retain each standalone harness's support namespace.

### Speeding up the gate: what has been tried

Read this before proposing another compiler-flag, build-profile or runner
change to make the gate faster. Those levers are close to exhausted; the
remaining time is in what the tests do, not in how they are compiled. Look
for ways to test the same behavior with less work (see "Where the test time
goes" below) before changing flags again.

The gate builds Click at `opt-level = 0`, its dependencies at
`opt-level = 2`, and the build script at `opt-level = 3` (`Cargo.toml`).

Measured on Claude Code cloud (4 vCPUs), one run each, tests run from nextest
binary metadata as `scripts/check.sh` runs them. "Small edit" appends one
unused function to `src/kernel/spec.rs`; #2488 (surface) and #2489 (kernel)
are real merged changes, each rebuilt from its parent's build:

| Profile | Cold build | Small edit | #2488 | #2489 | Unit/API tests | Fixture tests |
| --- | --- | --- | --- | --- | --- | --- |
| Click and dependencies at `opt-level = 0` | 358s | 95s | 87s | 156s | 414s | 399s |
| dependencies at `opt-level = 2` | 396s | — | 88s | 163s | 353s | 352s |
| everything at `opt-level = 1`, `lto = "off"` | 565s | 92s | 171s | 350s | 125s | 106s |

The small-edit and test columns are at `3c38b4b`, before the build-script
change; the other build columns are at `54347ef`, after it. All runs passed the same
7,597 unit/API tests and four fixture tests.

- **`opt-level = 1` for Click (PR #2486, reverted).** Tests ran about 3.5
  times faster, but a real change rebuilt about twice as slowly: an inlined
  function's edit invalidates every codegen unit it was inlined into. The
  unused-function benchmark hid this. In the merge queue, the shards saved
  about 100s and the build lost 130-190s (queue runs for #2488 and #2489:
  266s and 456s to build, against 129-265s before). Locally a full gate run
  still gained, but CI did not. ThinLTO at `opt-level = 1` added another 368s
  to a full rebuild.
- **Larger runners for `prepare`.** At `opt-level = 0` a small-edit rebuild
  used one core and a full Click rebuild 1.35 (`-Ztime-passes`: type and
  borrow checking and monomorphization collection are serial in rustc's front
  end; codegen took 118s of a 302s rebuild). More cores would not shorten it.
  At `opt-level = 1` rebuilds used about three cores, so a larger runner would
  help only that rejected configuration.
- **Linker.** Linking took 3s of a full rebuild; a faster linker cannot help.
- **Splitting the crate.** Not tried. The non-test kernel uses `crate::surface`
  in 3 places and `crate::languages` in 18, so a `click-kernel` crate is
  feasible, but 38 of the 52 merges before `3c38b4b` that changed `src/`
  changed non-test kernel code and would still rebuild everything downstream.
  A crate with in-module tests is also compiled twice, once as a dependency
  and once with its tests.
- **Build script (kept).** `build.rs` parsed the kernel and surface trees with
  unoptimized `syn` in 28s after every source edit, before rustc could start;
  at `opt-level = 3` it takes 6s with identical output.
- **Dependencies at `opt-level = 2` (kept).** Tests 12-15% faster, the cached
  `target/debug` 3.2 GiB instead of 3.7 GiB (CI restore time follows its
  size), and Click's own rebuilds within 5% (88s and 163s against 87s
  and 156s), at the cost of 38s more on a cold build.

#### Where the test time goes

Leads for test-level work, from the `opt-level = 0` run at `3c38b4b` on
Claude Code cloud and the merge-queue runs before PR #2486. "Test-seconds"
sums nextest's per-test durations while the gate runs tests in parallel.

- **Unit/API tests (1,652 test-seconds).** `surface::tests` holds 639 of them
  across 1,143 tests; `gate_tests::rust_import` 286 across only 79 tests,
  each starting Charon; `gate_tests::cpp_import` 98 across 176. On this
  machine 953 tests took half a second or more, 1,093 test-seconds in all,
  although the gate's rule moves such tests to nightly: the rule's wall-clock
  measure depends on the machine and load it was taken on.
- **Standard-library setup (measured at `fe8c6d9`).** nextest runs each test
  in its own process, and the parsed Click library is cached per process, so
  1,578 unit tests each parsed the whole library: 393 of 1,299 test-seconds,
  and a median 65% of each such test. Parsing library proof bodies, which
  ordinary verification does not read, was 44% of that load. A constructor
  lookahead that scanned to the end of the file after every `x < y` was
  another 24%; it now stops at the end of the comparison's proposition, and
  a cold load takes 242-255ms instead of 317-364ms. Short surface tests now
  share one load per batch ("Batching short tests").
- **mdtests (1,142 test-seconds, 5,065 files).** The slowest files take 6-12s
  each: `consumed_population_predicate_rejects_missing_consumption.md`,
  `authority_pool_control_missing_consumption.md`,
  `c_pointer_field_subrange_write_preserves_resources.md`,
  `an_interface_fact_needs_its_terms_defined_in_each_arm.md` and
  `array_fact_does_not_survive_a_branch_that_may_write_it.md`.
- **Examples (384 test-seconds, 58 projects).** `arena` takes 80s and
  `rbtree/rbtree-model` 53s. `EXAMPLE_PARTITION` once took every n-th
  sorted name, which put both in shard 2/2: 248 test-seconds against 136, the
  cause of CI's 113s and 59s examples shards. It now balances the shards by
  `EXAMPLE_COSTS` in `tests/examples.rs`.
- **Shard overhead.** Each of the 14 CI shards spends 20-30s on checkout,
  artifact download and setup. A Rust shard spent 11s downloading Charon and
  14s restoring its compiler runtime to run 23s of tests.

Unexplored directions: weight-aware fixture partitions; fewer, fuller Rust
shards; sharing one Charon extraction or verified library across the tests
that repeat it; per-test coverage to find tests whose covered behavior a
cheaper test already checks; and a machine-independent cost measure (work
counters or CPU time) for the half-second rule.

### Batching short tests

nextest starts a process per test, and each process that verifies anything
first parses the Click library (about 250ms in the gate's build). With
`fast-gate`, short tests in `src/surface/tests/` therefore run in batches of
four (five where one case would be left alone), so a batch parses the library
once. The batched files are `diagnostic_tests.rs`, `expansion_tests.rs`,
`surface_syntax.rs`, `contract_tests.rs`, `execution_tests.rs`,
`loop_tests.rs`, `project_tests.rs`, `preservation.rs` and the
files under `tactic_tests/`. The initial rollout covered 1,000 cases in
253 batches. The expansion API tests in `src/surface/expansion/tests.rs`
reuse the same runner and inventory macro for 69 short cases in 17 batches.
The authority private-body and transfer-wrapper tests, contract-closing
tests, and resource-parameter tests share library setup across another
54 cases in 14 batches.

Each case starts on a fresh 8 MiB-stack thread, retaining thread-local
isolation while sharing the immutable library-syntax cache across cases.
Lowered environments, proof state, and certificates remain session-local.
The original test bodies and assertions are unchanged. A batched test carries
`#[cfg_attr(feature = "fast-gate", ignore = "covered by <marker>NN")]`, so it
is ignored only in `fast-gate`; ordinary and nightly builds run it normally.
To run one individually in a fast-gate build, select its exact name and add
`--ignored`. Batch output names each case, its elapsed time, and any failure.

A file declares its batches with `test_batches!`
(`src/surface/tests.rs`), which also defines
`batch_inventory_covers_each_ignored_case_once`: the registry must cover
every annotated test of the file exactly once. A new test without the
annotation runs individually; add it to a batch only if it is short. Tests
with other attributes, a return type, or a second or more of run time were
left individual.

The half-second eligibility policy applies to individual cases, not the sum
of a batch. Batches keep nextest's existing 30-second process containment:
serial execution makes this an upper bound on any constituent case too.
No verifier work limits or nextest timeouts are increased. Keep batches small
so they distribute across CI partitions and do not hide slow cases.

Measured on Claude Code cloud (4 vCPUs) at `e01ca81`, one run each: batching
the 903 cases outside `diagnostic_tests.rs` took the unit/API suite from
1,265 to 1,091 test-seconds and from 317s to 267s of wall clock; the slowest
batch took 2.7s.

### Keep stress sizes out of the gate

Use one fixture generator for a small gate regression and its full nightly
stress range. Keep deterministic cost assertions on the gate sizes when they
still detect the regression; do not replace scaling checks with elapsed-time
thresholds. Include the largest sizes nightly, with the original assertions.
For full expansion/replay audits, keep the small positive and negative proof
regressions in the gate and run the multi-size audit nightly.

The gate still proves every standard-library theorem through
`standard_library_theorems_are_proved_by_their_own_entry_point`. Ordinary
verification trusts those dependency declarations, so moving this test to
nightly would remove foundational coverage from pull requests.

At `2ba6b3961`, a Linux x86-64 Intel Xeon Platinum 8573C host with a
four-CPU quota and 16 GiB RAM ran all 8,574 unit/API tests in 601.318s with
four workers (2,401.294 summed test-seconds). This excludes compilation and
the Markdown/example-project corpus harnesses. Tool and frontend caches were
warm; the ordinary unoptimized `fast-gate` test binary was reused through
`nextest --binaries-metadata`.

Single serial measurements before/after the test cleanup at that base:

| Gate workload | Before | After | Full-size coverage |
| --- | ---: | ---: | --- |
| Surface depth consumption case | 15.597s | 0.033s | Original parser limits nightly |
| Narrow-store constant-query scaling | 8.135s | 0.230s | Original 16/64/256/1,024 histories nightly |
| Separately declared invariant closure | 9.377s audit | 0.089s smoke | Original 8/16/32-declaration counter loop nightly |
| Balanced/skewed/projection transport scaling | 18.399s combined | Existing small regressions | Original expansion and strict cold replay audits nightly |

The eight selected gate tests took 70.324s before; their four replacements
and retained tests took 26.689s. These observations measure gate workload;
the complete suite was not timed again after the cleanup. The unchanged
library-proof test varied from 13.020s to 17.968s, so use CI measurements to
judge the overall effect. Measurements precede rebasing onto later upstream
changes.

`CLICK_TIMINGS=1` on the library-proof test attributed 7.563s to integer
proofs and 4.979s to formatting proofs across 206 theorem completions. Inspect
those individual proof scripts before changing the library check's gate
coverage; the remaining modules together took about half a second.

The complete signed/unsigned order-chain scaling audit (8/16/24/32 edges)
and proof-if context audit (1/2/4/8 earlier facts, with and without a split)
also run nightly. Theorem-based order proofs and
proof-if expansion regressions remain in the gate. The split fixture proves
its shared nonnegative bound once and uses explicit transitivity for each
original earlier fact, preserving the symbolic loop variable, C program,
contract, size range, and context-growth assertion.

The narrow-cast word-interning regression retains its per-cast work bounds
for independent casts, nested cast chains, and cross-signedness widening at
sizes 8/16 in the gate. Original 64/256/512 cases run separately nightly;
the helper and its original cost bounds are unchanged. The complete ordinary
fold/unfold selected-guard audit (4/16/64/256 unrelated requirements) also runs
nightly. Small ordinary-fold positive, invalid-value, missing-guard, and strict
certificate-replay checks remain in the gate.

Four loop expansion tests reuse the certificates returned by their existing
whole-source verification through `expand_checked_grouped_claim`. They retain
fresh verification of the generated source, negative checks, the zero-planning
assertion, and the nested-loop expansion-idempotence check. This avoids another
search for an input proof that the same test just checked. Three are gate cases;
the duplicate-invariant audit was already nightly and stays there.

Each of the four symbolic-upper-bound expansion variants contains one theorem
and one ensure. Selected-claim expansion verifies that input, so those cases
omit a preceding duplicate verification. Every generated proof still rechecks
with zero planning, and each forged tighter bound must fail.
Two interleaved serial runs using retained before/after binaries took
6.790/6.788s before and 5.931/5.472s after removing that duplicate pass.

On the same four-CPU host and cached unoptimized fast-gate binary setup,
the cast and selected-guard selection at `cff495519` took 5.787s wall and
18.666 summed test-seconds before this gate/nightly split; afterward, the two
retained gate sizes took 0.328s wall and 0.451 summed test-seconds. These are
selected test observations, not whole-gate timings. Loop certificate reuse is also
measured before the next upstream refresh: one serial before/after pair for
the four cases took 16.968s/14.096s, including the nightly duplicate-invariant
audit. Retain the explicit proof checks rather than treating those variable
wall times as a scaling assertion.

With the cast/fold/loop changes above on upstream `a1b9ea190`, before the
symbolic-upper-bound cleanup, a cached
four-worker unit/API run passed 8,116 tests in 444.876s (1,773.878 summed
test-seconds). It excludes compilation and every `gate_tests::` integration
or corpus harness. This is a current snapshot with a different test inventory
from the earlier 8,574-test baseline, not a controlled overall speedup ratio.
The library theorem proof took 15.206s and stays in the gate. Remaining leads
include the sibling-C-if preservation expansion (9.430s) and the 384-case
bitwise-conditional round-trip matrix (7.685s); inspect proof/setup reuse or
retain a compact gate selection with the complete matrix nightly.

### Sharing setup in expansion API tests

The batch runner and inventory macro are visible within the test-only Surface
module so API test modules can reuse them. Each case still runs on a fresh
8 MiB thread; only immutable library syntax is shared between cases. The
inventory checks every annotated case appears exactly once. Tests without
`fast-gate` still run the original individual cases, and the existing nightly
cases keep their nightly status.

The signed and unsigned 64-bit expansion tests also avoid proving their sole
input claim twice. Claim expansion verifies that input itself. Both tests
still independently verify the generated proof, inspect its bridge steps,
and reject the proof with its listed overflow bound removed.

Measured on Linux x86-64, Intel Xeon Platinum 8573C, four-CPU quota / 16 GiB,
with the ordinary unoptimized fast-gate profile, cached binaries and warm tool
caches. The verifier and expansion API fixtures match `4f614f04e`; the baseline
binary is the tested #3154 tree (`c7f0572c817bb00db29ebc82f1e3c747a1136329`).
The following are single observations with four test workers, not full-gate
or CI timings:

| Expansion API gate selection | nextest entries | Underlying cases | Summed test seconds | Wall time |
| --- | ---: | ---: | ---: | ---: |
| Before | 124 | 124 | 99.464 | 26.044s |
| 69 cases batched, other cases retained | 73 | 124 plus batch inventory | 69.303 | 18.540s |
| Batching and duplicate input-proof removal | 73 | 124 plus batch inventory | 63.729 | 16.959s |

The first run immediately after linking took 27.933s; use unchanged reruns for
this execution-floor comparison. The expansion API cleanup preserved gate/nightly coverage; compiler flags,
work budgets, and timeouts stayed unchanged.

For the two wide-integer cases, retained before/after binaries were run in
interleaved order, three runs of each with one test worker. Median per-case
times were 3.102s to 2.326s for `int64` and 2.623s to 2.186s for `uint64`.
The fixtures each contain one theorem and one ensure, so the expansion's
selected-claim verification covers the same input as the removed direct call.
Do not remove a whole-file verification when it checks other declarations or
claims the selected expansion does not cover.

The expansion API module also loads its five Markdown proof fixtures at
runtime. They previously appeared in Rust's dependency file through
`include_str!`; all five disappear from that dependency file after this change.
In a controlled fixture-only edit (one trailing newline, then restored),
`scripts/fast-gate-build.sh` took 0.647s, emitted no Rust compilation, and kept
the executable's modification time unchanged. The fixture's API test still
passed. This measures the fixture-edit build step, not a complete gate run.

### Distinguish runner waits from test execution

Read job `created_at` and `started_at` separately from the test step's start
and end when measuring CI. In #3154's merge-queue run `44175737083`, unit
shard 4/6 waited 374s for a runner, then spent 88s in its test step; markdown
shard 1/5 waited 353s, then spent 102s in its test step. These observations
explain why reducing verifier work may have a modest effect on an individual
workflow's elapsed time under queue pressure. Evaluate shard count and job
scheduling against those waits as well as test execution, while retaining the
complete gate coverage.

### Profiling markdown fixture phases

Set `CLICK_MDTEST_PHASE_TIMINGS=1` to report Markdown reading, input preparation,
project loading, and verification separately. For a focused run:

```console
CLICK_MDTEST_PHASE_TIMINGS=1 MDTEST_FILTER=a_population_entry_count_is_spelled_in_a_diagnostic cargo test --lib --features fast-gate gate_tests::mdtests::mdtests -- --exact --nocapture
```

Combine this with `CLICK_TACTIC_WORK_REPORT=/tmp/mdtest-work` to record
verification work without disabling budgets. Reports are opt-in and do not
change fixture expectations. Diagnostic-only negative fixtures should fail
with a direct check when searching for the deliberately false goal is not
part of the behavior under test. Preserve the diagnostic assertion and the
state needed to exercise it; semantic rejection tests still need to test
the intended proof operation.

### CI preparation and test partitions

CI uses these internal modes for code-affecting changes:

- `--ci-quality` runs formatting, setup/build regressions, and documentation
  on its own runner, alongside preparation. It does not delay test runners.
- `--ci-prepare ARTIFACTS` builds both exporters and compiles the single
  fast-gate test executable into an archive. It does not execute tests.
- `--ci-shard ARTIFACTS SUITE [SHARD/TOTAL]` runs the selected archive tests
  without compiling Click or either exporter. Six deterministic nextest
  hash partitions cover the unit, C, and C++ import tests, and two more cover
  the Rust import tests, which alone need Charon; mdtests run on five
  runners, each taking every fifth file by `MDTEST_PARTITION`; examples run
  on two, split by `EXAMPLE_PARTITION` so that their recorded costs
  (`EXAMPLE_COSTS` in `tests/examples.rs`) balance. The build job saves its build state only
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

A push to `master` runs the build job alone, to save the build state that
pull requests and the merge queue restore. The merge queue already ran the
whole gate on that exact tree, and repeating it after every merge took a dozen
runners that gating runs then waited for. The post-merge job compiles the same
targets with `scripts/check.sh --ci-warm-cache` and skips packaging and
uploading test artifacts.

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
libraries in `rust-runtime.tar.zst` using `scripts/charon-runtime.sh` and both
Charon executables in `charon.tar.gz`. They form the separate `rust-toolchain`
artifact. The single `rust` shard downloads that artifact, validates the
compiler, target, and toolchain identity, and restores those libraries before
setup, so missing caches do not prevent test execution. Every other shard
downloads the test binaries alone. Unit shards use
`scripts/setup-environment.sh --unit-test-runner` to install Click's pinned
Rust toolchain before the search-boundary tests compile visibility probes.
This keeps rustup's first-use download outside each test's 30-second timeout;
an installation failure fails setup. Other archive runners install no compiler,
and no shard installs mdBook. Preparation installs Charon's pinned compiler with `rustc-dev`
and `rust-src`, builds Charon once, and archives it. The compiled-in profile owns extractor
pins, flags, and versioned adapter interpretations; the build script reads the
same profile. Cargo's extractor dependency pin is checked against it.

The build job caches dependencies, Click's own build artifacts, and
incremental compilation state under the compiler and dependency identity.
Each revision saves a new state and later runs restore the latest
compatible state. A separate frontend cache retains the C++ exporter and
its fingerprint plus Charon's pinned source checkout (including Git metadata).
It is keyed by frontend sources, build/setup scripts, the Rust frontend profile,
and runner OS/architecture, and published only by master. Build scripts still
validate the exporter fingerprint and Charon revision on every run. Restore
this cache after evaluating the Click build-cache key so Charon's Cargo files
do not alter that key. Cargo still checks source freshness and rebuilds changed
code. Build states can be large, so cache transfer and fresh-checkout
rebuild costs must be included
when comparing CI timings; a cold cache still builds everything normally.

GitHub checks out the same source revision at the same absolute path on every
runner, preserving fixture and exporter sysroot paths embedded at compile
time. Test archives are extracted at the checkout root for embedded CLI
paths. Temporary upload archives stay outside the build cache.

For docs-only changes, pull-request CI and the explicit
`scripts/check.sh --docs-only` path run only the focused documentation gate
described above. The merge queue always runs the full gate. The proof fixtures verify their inputs on every core. Judge
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
the pinned LLVM development packages, or the pinned LLVM release where
`apt.llvm.org` is unreachable. `scripts/check.sh` only looks tools up
and never reaches the network. Then run:

```console
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

Measure budgets with this command; `REPORT_DIR` is optional:

```text
scripts/measure-tactic-work.sh [REPORT_DIR]
```

It runs the mdtest and example harnesses with
`CLICK_DISABLE_TACTIC_BUDGETS=1`, so no cost is clipped (the harnesses' own
pinned budgets step aside too), and with `CLICK_TACTIC_WORK_REPORT` set, so
each fixture records in process the work every tactic charged and writes it
to `REPORT_DIR` (default: a fresh directory under `target/tactic-work/`). It
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
typed solve closure as a closing probe, and much of that closure's cost was
uncharged premise surface synthesis. The probe now asks the direct logical
closer, and the synthesis is lazy and charged, so the heaviest arena `have`
(`click profile`, after this calibration) is 488,691 units with every unit
counted, and the heaviest smart tactic is a failed mdtest closure search
(1,040,194 units under the former `solve` spelling). The slow tactics listed
near it in `TacticWorkLimits::default` include a failed closure search and the
arena proofs' heaviest `have`s. The same run's `run`
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

### Scaling tests

A scaling test measures deterministic work at several input sizes and asserts
how it grows. Every one lives under `src/scaling_tests/`, whose tree mirrors
`src/`: the scaling tests at the top level of
`src/kernel/tests/resource_tests.rs` are in
`src/scaling_tests/kernel/tests/resource_tests.rs`, and those of an inline
module are in a file named after it, so the scaling tests of
`mod held_separation_tests` in `src/kernel/proof/facts.rs` are in
`src/scaling_tests/kernel/proof/facts/held_separation_tests.rs`. The module
whose behavior a file measures includes it in a child module named
`scaling_tests`:

```rust
#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/proof/facts/held_separation_tests.rs");
}
```

so the tests keep their module's private access through `use super::*`. A
whole file of scaling tests is declared with `#[path]` instead, keeping its
module name, which ends in `scaling_tests`. `include!` rather than `#[path]`
is needed because a path inside an inline module is resolved through
directories that need not exist. Every scaling test's path therefore contains
`scaling_tests`, and one filter runs the whole set:

```console
cargo nextest run --lib -E 'test(/scaling_tests/)'
```

`cargo fmt` does not follow `include!`, so `scripts/check.sh` formats
`src/scaling_tests/` with `rustfmt` directly, and the documentation test
`every_scaling_test_file_is_included_by_its_module` fails on a file no module
includes. Before changing a hot path, read the scaling tests of the modules it
touches; add new ones beside them.

Most scaling tests measure one kernel operation beside unrelated state built
in advance. Growth that comes from the proof itself, such as state each
statement leaves for the next, needs whole functions:
`src/scaling_tests/surface/tests/step_shape_scaling_tests.rs` verifies the
shapes of `scripts/step-scaling-hunt.py` at gate sizes with one `step()` per
statement. Its main check needs one size. Steps that execute the same
statement at different positions (each `drop_box(p#)`, each call) must cost
the same, so a step whose work moves the same way by more than a small band
at each of its last positions depends on how many statements ran before it.
A warm-up, such as the first call or the first store into a block, jumps once
and then holds, which this does not flag. A slower drift, too small for the
band, still never falls and rises at most positions of the second half, which
the check also flags; a bounded window (a cost that climbs with the statements
near it, then holds) passes once the shape runs past it. Roles name statements
with each number replaced by one `#`, so `x9` and `x10` share a role. The proof's `unfold` and `fold`
tactics are held to the same rule, each tactic name one role in proof order.
Uncharged costs do not show in work; the script's mean step time is the check
for those. Shapes whose every step sees the
same growing state (unrelated facts, aliases, owned objects) compare one
step across two sizes instead. Known growth is asserted as still present
(`known_drift_` tests naming their issue or bug), so a fix fails the test that
records it and the record is updated with it. `step-scaling-hunt.py` runs the
same shapes at larger sizes, with timing, when a curve needs investigating.

The built-in standard library is parsed and resource-expanded once per process.
Only immutable surface declarations are shared; each verification constructs
its own environments and kernel session. The initialization-count regression
checks 1, 2, 4, and 8 fixture threads, including successful and failing programs
with conflicting declaration names. Keep this reuse across fresh mdtest threads;
a thread-local cache would repeat setup for every fixture.

An optimization that changes a hot-path representation or algorithm should
include a generated deterministic-work regression at four or more input sizes.
Test independent dimensions rather than one realistic example: functions,
straight-line statements, facts, surface forms, resources, theorems, and
claims. Exclude fixed parsing/startup work where practical and assert the
growth ratio, not an elapsed-time threshold.

The intended bound for simple verification is output-sensitive `N log N` or
better. A benchmark that merely stays below the production deadline can still
hide quadratic growth and is not sufficient. Conversely, explicitly emitted
paths, quantified instances, premises, and definition members count as input
or output and may be charged accordingly.

Kernel memory states have such regressions in
`src/scaling_tests/kernel/tests/memory_scaling_tests.rs`: sequential stores into one block,
one store beside a growing number of unrelated cells, interning a one-store
derivative of an interned state, and deduplication of equal content reached
by different routes. The same file bounds by a constant plus a logarithm the
work of one C store, one call havoc and its checker, one free, and one typed
load into a heap block beside a growing number of unrelated live allocations,
and re-deriving one store from the same base (a statement planned and then
checked) beside a growing number of unrelated cells, which must also hand back
the first derivation's storage. Normalizing allocation tokens in distinct heap
blocks must stay linear in the tokens.

Resource-context validity has its own in
`src/scaling_tests/kernel/tests/resource_scaling_tests.rs`. Validity of a caller frame, and
composing one ensured range into it (a verified call's return), must cost
work that does not grow with unrelated owned allocations and instances beside
the target, nor with unrelated pointer equalities in the assumptions: the
check reads only indexed candidates (identities held twice or with invalid
access, blocks owning two or more ranges, and aliased bases, driven from the
smaller of the bases and the equalities). A companion test finds each
violation kind beside many unrelated resources from either side of the alias
walk. A call that only `views` a heap range, with the observable projection
of its caller's resources after it, must likewise cost the same work beside
2, 4, 8, and 16 unrelated live allocations.

End to end, `roundtrip_extra_copy_stays_nearly_flat_beside_unrelated_allocations`
in `src/scaling_tests/surface/tests/scaling_tests.rs` verifies the frozen byte-representation
round trip beside 2, 4, 8, and 16 unrelated live heap allocations, with and
without one extra fixed `memcpy`, and bounds the extra copy's marginal work by
an eighth above its smallest value. It guards the collapse of the quadratic
fact comparison at every free and of the whole-context resource validity
sweep at every call; it is not the logarithmic contract, which the smart
execution planner (`SmartExecute`) does not yet meet (its test comment names the remaining
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

### The goal-closure eval

`evals/solve.py` measures, for a sample of the hand-written `have`
statements in the examples, how many the omitted proof `have P;` proves where
they stand and how many can be deleted with the proof still verifying, against a committed
baseline. A change to the implicit closer, `close()`, or what they rely on quotes its result,
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
One that grows is a defect with the shape as its reproduction: fix it with an
ordinary multi-size regression, or ask the user before filing it in `bugs/`. A step whose own input
grows, such as one statement summing N fields or a `return` that releases N
locals, grows linearly by design; read the per-size output before filing.

Time is reported beside work because work counts only what is charged. The
hunt's first finding was invisible to it: an atomic proposition hashed its
debug text, which printed every memory state it named, so each call in a
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

This state also gives a concrete interpretation to an aspirational target:
10,000 selected lines in three seconds is about 3,300 lines per second, roughly
six to seven times this corpus-wide baseline. Re-measure after substantial
checker or corpus changes instead of treating the dated numbers as permanent.

The direct CLI is itself the bounding mechanism: `click verify --time-limit`
cooperatively interrupts execution, proposition derivation, memory resolution,
and resource search. Do not wrap Click in an external timeout command; a proof
search that outlives the CLI limit is a Click tooling bug.

## Hidden prerequisite ratchet

A simple tactic must close each requirement by an exact or indexed check;
`step()` and the `loop {}` walk both check statements under a search-free
policy. Where checking still derives a prerequisite by a search whose result
the proof does not retain, it counts the derivation by route and top rule
(`instrumentation::HiddenPrerequisiteRoute`). The fixture harnesses take
that census after an unfiltered run and compare it with
`HIDDEN_PREREQUISITE_BASELINE` in `tests/mdtests.rs` and `tests/examples.rs`.
The comparison is exact: a count that rose must not land, and a count that
fell lowers its pin in the same change. A partitioned CI
shard (`MDTEST_PARTITION`, `EXAMPLE_PARTITION`) sees part of the corpus, so it
fails only when its own count exceeds a whole-corpus pin; an unpartitioned
run, such as a local `scripts/check.sh`, checks both directions. Library tests read
the same events per step through `collect_planning_statement_transitions`,
which records the claim and step of each hidden derivation. The kernel's own
condition evaluation asks only the difference graph and its keyed rules, so
it derives nothing hidden
([verification efficiency](verification-efficiency.md#condition-decisions-in-simple-checking)).
The `TacticSearch` route counts a resource, separation or
loadable-memory obligation a step proves by searching the proof context
outside its fast path, under a smart tactic's policy. A simple tactic never
searches: its premise checks are an exact lookup and the kernel's condition
decision (`holds_by_lookup_or_decision`), and a premise they miss is refused or
left to a case split. A simple tactic may consult the proof context through the kernel's
indexed, bounded decisions, as a step's fast path does: the condition
decision and the checked load equality over recorded memory history. Those
are not searches and are not counted; only a proposition `ProofSearch` call is.

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
one Click block, and one expected result. A minimal file has these three
blocks:

<!-- verified-example: mdtests/mdtest_file_format.md -->
```c
int32 example() {
    return 0;
}
```

<!-- verified-example: mdtests/mdtest_file_format.md -->
```click
verifying "example.c";

int32 example() {
    ensures result == 0;
}
```

```expect
pass
```

In the file itself the C fence's info string also names the source,
`filename=example.c`, so the Click block's `verifying` clause can refer to it.
`mdtests/mdtest_file_format.md` is this example as a complete file.

Negative tests use an expected diagnostic substring:

```text
fail: expected diagnostic substring
```

### Writing quick solve tests

A Quick Solve Test isolates one small inference that `close()` should check, find, or promptly refuse. Add `quick-solve` to the opening
`click` fence and use a normal `expect` block. Write the essential premises and
one explicit closer that the verifier reaches exactly once. Keep any C setup
to the operation needed to establish the premises. Name the file for the rule
it exercises so related tests and near misses are easy to find.

Write the closer as a step in a tactic script. Click profiles the short form
`have P by close()` under `have`, so it does not supply a solve sample.

The mdtest gate checks the ordinary proof verdict and a shared limit of
50,000 deterministic work units for the written closer, including tactics
and certificate work it runs. A limit refusal fails the test even when the
fixture expects a proof refusal. The nightly expansion audit checks replay.
Use the scaling tests when the question is how inference cost grows with
unrelated input.

Run just this group with:

```sh
MDTEST_QUICK_SOLVE=1 cargo test --lib --features fast-gate gate_tests::mdtests::mdtests -- --exact
```

`MDTEST_FILTER` narrows that group by file name. Set
`CLICK_TACTIC_WORK_REPORT` to a directory to inspect the per-tactic samples.
The report's last column includes nested work. For calibration,
`CLICK_DISABLE_TACTIC_BUDGETS=1` disables the cost verdict.

A fixture that exercises direct checking can mark its opening Click fence
`click checked-only`. The mdtest gate then verifies the fixture under the
same no-search policy as `click verify --checked-only`.

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
profile=scalar_int32`; keep the usual Click and expected-result blocks. Several
clients are separated by `;`, `function=round_trip;pushed_size`.

`profile=normal_only` uses the exception-disabled baseline; `scalar_int32`
enables typed `int` throw/catch. Each C++ mdtest's lock and semantic artifact
are checked in under `mdtests/cpp-imports/<mdtest>/`, so the mdtest gate and
the profile, expand, and audit commands load them without a compiler. A C++
mdtest outside the corpus has none and needs `CLICK_CPP_EXPORTER`. After
adding a C++ mdtest, changing its C++ fence, or changing the exporter, run
`scripts/refresh-cpp-imports.sh` (LLVM 19.1.7) and commit the result. Where the
exporter is available, `cpp_mdtest_imports_match_the_pinned_exporter` in
`tests/mdtests.rs` fails on a stale, missing or orphaned import.
The C++ and C fences cannot be mixed in one mdtest. See
`mdtests/cpp_scalar_catch.md` for a real exception path.

## Cross-language integer fixture

`examples/integer-languages/` holds the same small integer programs in C, C++
and Rust (`c/integers.c`, `cpp/integers.cpp`, `rust/integers.rs`) and one
sidecar per language (`c/c.click`, `cpp/cpp.click`, `rust/rust.click`) stating
the same claims: signed arithmetic under an exact overflow precondition,
unsigned wrapping through `integer::uint32_wrapping_*`, `uint32` values above
`INT32_MAX`, sign conversions, signed and unsigned division, remainder and
right shift, narrowing, 64-bit arithmetic, signed against unsigned order,
and `Bool`: negation, conjunction, an integer's truth, a `Bool`'s integer
value and their sum, and a selection by a `Bool`.
It is the language-level counterpart of the kernel's per-format matrix
(`src/kernel/machine_integer/matrix_tests.rs`). The example harness verifies
the three parts as separate examples, so a language that falls behind fails
there, naming its sidecar and function. `tests/examples/integer_languages.rs`
lists every case with each language's gap, if any, and
`claims_agree_across_languages` requires the same signature (Rust types read
as Click's) and contract lines in every language.

A gap is named, not omitted: the case's claims and proof are in that
language's `.click-gap` file, which the corpus tools do not read; a language
with no gap has none (currently C and Rust). Rust wrapping arithmetic is
part of the ordinary fixture, with the same contracts as C and C++. A
verification gap must still be refused at its recorded goal, checked in the
nightly (`verification_gaps_are_still_refused_in_every_language`); an import gap must still be refused by the front end, checked with
the pinned exporter in the gate where `CLICK_CPP_EXPORTER` is set. Closing a gap fails
these checks until the case moves into the sidecar. The C++ and Rust imports
are checked in, so the gate loads them offline. The nightly
`cpp_import_matches_the_pinned_exporter` and
`rust_import_matches_live_charon_extraction` compare them with a fresh export
and extraction. After changing a source, run `click capture` on its
directory with its toolchain.

## Width-uniformity fixture

`src/surface/tests/width_uniformity.rs` states each machine-integer lemma
family of `library/integer.click` (comparison bridges, order laws, the
range, in-range sum, difference and product identities, increment and
predecessor forms, definedness forms, the round trip) at every format in
`machine_integer::FORMATS` and proves it by the omitted proof, with no
`import click::integer`, so no library lemma is in scope. It is the
surface counterpart of the kernel's per-format matrix
(`src/kernel/machine_integer/matrix_tests.rs`), and it replaces a generic
`T: intn` library mechanism (maintainer, 2026-11-09). Statements are honest
at each format: in-range identities take Integer-range premises, never
`defined`; arithmetic is written `let r: T = a + b;`, the native operator
at `T` (inside `to_integer(...)` an 8- or 16-bit sum is C's promoted `int32`
sum); `defined(...)` families apply only where
`representation::files_definedness` holds (`int32`, `int64`).

Each family/format pair is proved or excluded with a reason (`Exclusion`).
The gate runs `every_format_is_tested_and_family_names_are_unique`, which
fails on a format with no test, and
`width_family_representatives_close_at_every_format`, which proves the
`<=` bridge and the range at all ten formats in about 0.4s, most of it the
first verification's library setup. The per-format
`width_families_close_at_*` tests (0.4s to 1.3s each) are nightly.

## Example project tests

Example projects live under `examples/`. The integration test in
`tests/examples.rs` verifies `.click` sidecars against C files in each immediate
project directory.

Use example projects for larger library-shaped fixtures. Keep them small enough
that a reader can understand the proof boundary.

### Verifying one file or project directly

`click verify` is the plain verification command the expansion workflow ends
with. It takes either a sidecar or a directory:

```console
click verify examples/input-cursor/input_cursor.click
click verify examples/input-cursor
click verify examples
```

A bare sidecar path verifies the proof units owned by that file. A
`:LINE:COLUMN` suffix verifies only the proof unit containing that one-based
source location. Imported theorem statements and unselected called-function
contracts are knowns, not recursively selected proofs. This is the same
location scheme `click profile`, `click expand`, and `click audit` use, and the
targeted entry point the audit's cold reverification runs.

A function's pointer input names depend on its kernel name and parameter index,
including the implicit construction-result parameter. They occupy the reserved
`2^34 .. 2^40` range, below load variables and above frontend, callback, termination,
and resource-matching variables. Allocation order, earlier functions, and selected-unit
verification do not change them. The input registry rejects hash collisions
instead of aliasing inputs or probing for an order-dependent replacement.
Metadata is cleared alongside the kernel tables when a fresh
`VerificationSession` starts. Verification prepares all functions' input
metadata before any proof runs.

Load names and state content hashes derive from input names, and closers
search facts and recorded states in an order that follows them.
The nightly `a_functions_tactic_work_does_not_grow_with_earlier_unrelated_functions`
checks exact input-name and per-tactic work equality between whole-file and
selected-unit verification beside 1, 2, 4, and 8 unrelated earlier functions,
including reversed declaration order. It uses the original eight-tactic
reproduction, including the single-earlier-function case.
Before return, signed-order automation selects indexed bounds before broad
atomic premise raising. Existing named rules get first choice over that
compact context, followed by the checked ordinary arithmetic proof. Terminal
outcomes retain their result-aware equality rewrites and source-anchoring
routes before that arithmetic fallback.

A directory verifies every sidecar under it, grouped by project
(`click::cli::select_sidecars`). A declaration module (imports, types,
predicates, pure functions, and resources only) is checked through its
importers and is not an entry. The examples gate selects entries the same way
and schedules each directory that directly holds a sidecar on its own, named
by its path below `examples/` (`rbtree/rbtree-insert`), so the parts of one
project can be run, skipped or quarantined separately.
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

```console
click verify path/to/file.click
click expand --in-place path/to/file.click:LINE:COLUMN
click verify path/to/file.click
```

When profiling attributes aggregate cost to a claim containing many individually
small smart tactics, expand the complete claim in one checked operation:

```console
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

```console
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

See the [profile reference](../reference/cli/profile.md#options-and-defaults)
for the per-class reporting thresholds and the crash-containment limit.
These settings control what the profile reports and when it stops.
Verification verdicts use deterministic work budgets.

The verifier emits each tactic's class as a structured event. The report uses
that class to prescribe the next action:

- Successful `SMART` hotspots in fully verified targets are expansion
  candidates. The report prints pasteable commands that write a sibling
  artifact, verify it, and reprofile that exact artifact with the same limits.
  Locked imports instead use `--in-place` and recheck the same sidecar, keeping
  its manifest and artifacts at their anchored name and location.
  A successful step observed before a later correctness failure or timeout is
  diagnostic only and produces no expansion command. Failed smart search has
  no successful proof; normally decompose the proof, or write the argument a
  search miss of an elided form names. An interrupted search is a tooling bug
  only when it ignores or badly overshoots its enforced bound. A smart site is
  a written `close()` or `step_until`, the implicit tail or closer, or a
  simple tactic written with an elided argument (see
  [`click profile`](../reference/cli/profile.md#report-interpretation)).
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

```console
scripts/profile-samply.sh examples/binary-tree
```

This builds the `profiling` cargo profile (optimized, with symbols) and opens
the recording in the Firefox Profiler; `--save-only` writes
`target/profiling/click.samply.json` instead. Install samply once with
`cargo install samply --locked`. A sampling profile answers "which function is
hot", never "which step exceeded its budget": those are different questions,
and the budget one belongs to `click profile`.

### Comparing verifier performance

Build the two Click executables with the same Rust toolchain and optimized
Cargo profile, in separate target directories. Run the harness from the
common workload checkout.

```console
scripts/benchmark-verify.py --baseline /path/to/base/click --candidate /path/to/new/click
```

With no target arguments, the harness runs Arena, Owned Vector, and Rust
Iterators. Pass one or more sidecar, mdtest, or project paths to use a
smaller reproduction or a different workload. Use binaries that support
`click verify --locked` and prepare any required captures before running.
Both variants read these same targets and run full verification with the
same limits. Use `--candidate-env NAME=VALUE` with no `--candidate` to compare
two runtime configurations of the same binary. `--baseline-env` sets
overrides for the first variant. The report records these overrides.

The harness runs one warmup per variant and five timed pairs per workload
by default. Pairs alternate baseline–candidate and candidate–baseline.
`--warmups` and `--pairs` override these counts. Warmups and the separate
`CLICK_TIMINGS=1` pass do not enter the timing samples. CPU and wall times
cover the full command, including source loading and any Git bookkeeping.
The reported work sums completed tactics' exclusive work charges. The
raw logs preserve named operation counters and phase timings for
investigating costs outside tactics.

Use `--output` to retain the report at a named directory. The default is a
fresh temporary directory. The report contains run order, raw samples,
proof counts, command logs, executable checksums, and the workload
checkout revision when available. A verifier failure or unequal proof
counts stops the comparison and leaves the logs for inspection.

Compare paired differences with the spread of each variant's timings.
Use [the benchmarking skill](https://github.com/clicklang/click/blob/master/.agents/skills/benchmarking/SKILL.md)
for interpretation and keep wall-clock measurements out of the regular
gate.

### Dependency-aware incremental verification

After a clean full verification, Click records a small atomic success marker
inside Git metadata for that exact commit, sidecar, and Click executable. It
records a marker only when the sidecar and its declared C sources match `HEAD`;
interrupted or dirty verification cannot attest a baseline.

Use the attested commit as a semantic comparison point:

```console
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

```console
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

Each selected claim is audited as a batch:

1. **Expansion** captures the whole claim when all sites are selected, or
   captures the selected sites together when a cursor or site cap limits the
   selection. The rewrite must round-trip through the ordinary Click parser.
2. **Fixed point** checks that a whole-claim rewrite contains only explicit
   tactics. With a partial selection, the check covers the replacement
   regions and leaves unselected automation available.
3. **Retained replay** checks that the rewritten source matches the baseline
   outside the selected proof unit and reverifies that unit using the
   certified dependency environment. The session runs on its own thread
   because the environment refers to that thread's kernel tables.
4. **Cold replay** verifies the rewritten unit without the retained session.
   Whole-claim replay disables the implicit closer and monitors discovery in
   the selected claim and its nested proofs. Neighboring claims and modeled
   workers use their ordinary verification policy. A missing runtime claim
   label fails. The original's cold work is measured for the report.

A passing audit prints one bounded row per claim by default:

```text
CLAIM [2/25] examples/owned-vector/vector.click  vector_copy.contract (1 sites) ... ok (1 sites)
```

Repeat `--claim LABEL` to select exact named proof units. Unknown labels are an
error; labels present in multiple sidecars are rejected as ambiguous unless the
audit target is narrowed to one sidecar or the claim is selected by location,
`--claim FILE:LINE[:COLUMN]`. `--verbose` adds the batch's phase costs, proof
size, and throughput to its progress row.

### Small-stack canary

Checked verification advances a persistent `Proof`; its execution state
(`ExecutionProofState`) is carried by value through the driver frames.
`nested_conjunction_body_parsing_uses_small_frames_and_linear_work` parses
nested proof bodies on an explicit 1.75 MiB thread stack, below libtest's
2 MiB default, and
`nested_solve_derivations_keep_rule_temporaries_off_the_recursive_stack` checks
nested solve derivations on the same budget. Recalibrate on the CI platform
before tightening it. The outlined proof-rule and driver adapters
keep rule-local enum and proposition payloads out of their dispatchers'
frames; they are stable stack budget boundaries. Changes to those boundaries
must keep the small-stack canary green.

### Deterministic checking work

Cold replay checks the expanded proof against the verification phase budget,
the per-tactic budgets, and each instrumented checked operation's own
allowance. A full claim audit also rejects monitored discovery during replay.
These checks use deterministic work units. Add multi-size regressions for
operations whose cost might grow with unrelated context.

Audit records the original cold work for diagnosis. An increase above both
twice the original work and the original plus the configured
`--performance-slack` (default 10,000 units) is highlighted on a passing claim.
Verbose output includes the expanded proof's size and checking throughput.
For a claim failure, the reproduction command selects the affected claim or
its original partial selection.

Each phase has a deterministic work budget: `--session-work-limit` (default
100 million units, spent separately by each source's smart-site inventory
and session initialization), `--expansion-work-limit` and `--verification-work-limit`
(default 50 million each). On 2026-09-26 the largest session measured was
`examples/arena`'s at 6.5 million units, and the largest expansion or
proof-unit verification under half a million. A process's first verification
also charges the one-time load of the built-in standard library, about 24,000
units. Audit initializes its session before measuring either cold proof, so
both replay measurements use an initialized standard library.

A phase's wall-clock limit is crash containment only (default 10 minutes
each), for a hung or CPU-starved run. The whole run is also bounded by
`--time-limit` (default 10 minutes). Every blocking phase observes the
remaining whole-run time cooperatively, including session initialization and
cold verification. Each phase's process watchdog retains its configured crash
bound. Reaching the whole-run deadline stops at the current inclusive cursor,
prints a summary and resume command, and exits unsuccessfully without counting
deadline exhaustion as a Click check failure. An interruption during preparation
prints a restart of the same selection, preserving any supplied cursor.

### Time limits and resuming

| Option | Default | Bounds |
| --- | --- | --- |
| `--session-work-limit` | 100000000 | work of one source's smart-site inventory, and of its original-sidecar session initialization |
| `--expansion-work-limit` | 50000000 | work of one expansion, and of the re-expansion check |
| `--verification-work-limit` | 50000000 | work of one retained or cold proof-unit verification |
| `--performance-slack` | 10000 | minimum work increase to highlight, beside the 2x ratio |
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

```console
click audit --session-work-limit 100000000 --expansion-work-limit 50000000 \
  --verification-work-limit 50000000 --performance-slack 10000 \
  --session-time-limit 10m --expansion-time-limit 10m \
  --verification-time-limit 10m --time-limit 10m \
  --start-at path/to/file.click:LINE:COLUMN examples
```

`--start-at` is inclusive, so fixing a failure and running the suggested
command retests that same site before continuing. The cursor also skips
session initialization for preceding files. `--keep-going` collects failures
and continues, including per-file input/runtime/inventory errors and implicit
proof-location errors during discovery. Each failed file or claim is reported
and counted in the final failure verdict; other files and discoverable claims
are still audited. Invalid command selections and the whole-run deadline still
stop the run. The nightly audit uses this mode. Use `--max-sites` only for a
deliberately partial diagnostic run; it prints the next cursor when the bound
is reached. A release or expansion-boundary audit should omit it and finish
one complete pass.

Every site starts from the unchanged baseline source, so an earlier rewrite
cannot hide or cause a later failure. With `--keep-going`, a failed session is
rebuilt from a fresh complete verification before the audit continues. The command exits
unsuccessfully if session initialization, expansion, parsing, source isolation,
proof-unit verification, the fixed-point check, discovery during complete
replay, a deterministic work allowance, or the run limit fails.

Proof scripts have no runtime semantics. Re-verifying the same isolated claim
is the semantic audit condition; requiring the automation and generated
explicit proof to visit byte-identical internal branch/path states would reject
valid expansions and is intentionally not an audit invariant.

## Unit tests

Rust unit tests are appropriate when the behavior is lower-level than a sidecar
can express clearly, such as parser details, kernel term simplification, or
specific reasoning helpers.

### Testing scoped loop-exit facts

Set `CLICK_SCOPED_LOOP_EXIT_FACTS=1` when running `click verify`, `click expand`,
or a focused mdtest run to exercise the experimental loop join. On the
loop continuation, it keeps only facts established on every incoming exit
and expressible in the enclosing proof. It compares checked facts in terms
of the joined state's values. The `otherwise` block still sees the
false-guard context it proves in.

```sh
CLICK_SCOPED_LOOP_EXIT_FACTS=1 click verify mdtests/loop_otherwise.md
```

## Test selection

When adding a feature, prefer this order:

1. Add or update an mdtest that demonstrates the user-visible behavior.
2. Add unit tests for lower-level parser or kernel behavior if needed.
3. Add or update an example project only when the feature changes the shape of
   realistic verification.
4. Update the relevant docs.

Mdtests are the main executable documentation for Click's proof surface.

## Rust release archive installation

The Rust frontend release workflow builds pinned Charon in release mode,
assembles one archive and checksum with the production packaging script, and
runs `tests/rust_release_install.rs` against those same files before upload.
Relevant packaging pull requests run the same check without publishing.
This dedicated target is outside the normal gate and full nightly fixture
list because it needs a release artifact explicitly; its ignored test fails
when `CLICK_RUST_FRONTEND_ARCHIVE` is absent rather than substituting debug
binaries. Run it locally with the pinned compiler installed:

```console
scripts/build-charon.sh --release
source scripts/charon-toolchain.sh
scripts/package-rust-frontend-archive.sh target/rust-release target/charon/release "$CHARON_SYSROOT"
CLICK_RUST_FRONTEND_ARCHIVE="$PWD/target/rust-release/click-rust-frontend-x86_64-unknown-linux-gnu.tar.gz" \
  cargo test --test rust_release_install rust_release_archive_installs_and_verifies -- --ignored
```

The test uses the real installer with a local fixture transport for curl;
checksum validation, archive extraction and installation are production code.
After installation the transport is removed. The installed Click then locks
and verifies the unchanged basic Rust example outside the checkout with no
rustup or compiler on PATH, and checks offline verification after deleting the
frontend. The check covers packaging only: proof regressions in the Adler-32
trials belong to nightly, including
`adler32_prepared_demonstration_verifies_offline`, which verifies the prepared
C/Rust checksum demonstration with the development binary.

## C++ release archive installation

The C++ frontend release workflow (`.github/workflows/cpp-frontend.yml`)
installs the pinned LLVM release, builds the self-contained exporter with
`scripts/build-cpp-exporter.sh --release`, packages one archive and checksum
with `scripts/package-cpp-frontend-archive.sh`, and runs
`tests/cpp_release_install.rs` against those files before upload. Like the
Rust check, it is outside the gate and the nightly target list, and fails
without `CLICK_CPP_FRONTEND_ARCHIVE`. The release link takes about two
minutes; it needs the pinned `ld.lld`, because the release's static Clang
libraries hold LLVM bitcode. Run it locally with:

```console
scripts/build-cpp-exporter.sh --release
scripts/package-cpp-frontend-archive.sh target/cpp-release target/cpp-exporter-release \
  /usr/lib/llvm-19/include/llvm/Support/LICENSE.TXT
CLICK_CPP_FRONTEND_ARCHIVE="$PWD/target/cpp-release/click-cpp-frontend-x86_64-unknown-linux-gnu.tar.gz" \
  cargo test --test cpp_release_install cpp_release_archive_installs_and_locks -- --ignored
```

The test installs through the real installer and fixture transport, moves
the Click home, and then, with an empty `PATH` and no `CLICK_CPP_EXPORTER`,
locks a copy of `examples/basic-cpp` with the installed exporter. The lock
and artifacts must equal the committed ones byte for byte, and all three
sidecars must verify, the last also after the front end is removed.
