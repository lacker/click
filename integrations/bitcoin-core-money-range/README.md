# Bitcoin Core `MoneyRange` on a macOS host

This opt-in integration example imports the unchanged inline `MoneyRange` from
Bitcoin Core v31.1 through a real `src/policy/feerate.cpp` CMake compilation
command. The host can be Apple Silicon macOS: Clang targets x86-64 Linux using
Linux headers from a pinned Debian sysroot. It does not claim to link or run
Bitcoin Core binaries.

The upstream tag is pinned to commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`. The expected SHA-256 values
are `624a30c64528ce9873a1e440039cd261db81deecf14ed3003c171f7c2039ca50`
for `src/consensus/amount.h` and
`a339052701a35a484a6d84e83d257ae643da2e2b635ccf105b44edf2f2ba30e8`
for `src/policy/feerate.cpp`. Check the commit and both hashes before importing;
do not copy the function into this example.

The tested toolchain was Homebrew Clang **19.1.7**, CMake **3.31.6**, and these
Debian Bookworm x86-64 development packages extracted into `inputs/sysroot`:

| Package | Version | SHA-256 of `.deb` |
| --- | --- | --- |
| `libc6-dev` | `2.36-9+deb12u14` | `0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae` |
| `linux-libc-dev` | `6.1.176-1` | `8bb258735b9dffbb111da778ebdd024750878e435ffd9dfcadcb6762ede6b4cf` |
| `libstdc++-12-dev` | `12.2.0-14+deb12u1` | `d28def6c23630432b57cb38a4c2fd67a79d4e0484027386ca6e8d6005c3d7a73` |
| `libgcc-12-dev` | `12.2.0-14+deb12u1` | `d720259380a84f2ffc6fe516eff5cbe9c8a005138e8d6a5748747ba4b3404a82` |
| `libboost1.74-dev` | `1.74.0+ds1-21` | `ba14fe04d7f138f874bd3ab3a20c4fd1e9f654e271449b8f3e48d20f942dbb93` |

## Project

[`click.project.json`](click.project.json) declares one C++ unit, `bitcoin`,
with exceptions and RTTI on as Bitcoin Core builds. Its `args` are the selected
`src/policy/feerate.cpp` command from Bitcoin Core's CMake-generated
compilation database, every argument in order with its paths relative to this
directory, `-O2` and the hardening flags included; Click supplies only the
driver, `--target=x86_64-unknown-linux-gnu`, `-std=c++20`, `-c` and `-o`. A
gate test checks that the arguments are exactly that command. Each source is a
Bitcoin header verified through `feerate.cpp`: `consensus/amount.h`
(`MoneyRange`), `serialize.h` (`GetSizeOfCompactSize`) and `util/feefrac.h`
(the `FeeFrac` operations, with `check.h`'s assertion admitted as a checked
library boundary).

The committed `.click/captures/manifest.json` and `.click/captures/bitcoin/` artifacts verify
offline. The lock rechecks the Bitcoin and sysroot files in this directory, so
extract the hermetic closure here first:

From this directory, with an installed `click`:

```sh
tar -xzf input-closure.tar.gz
click verify MoneyRange.click
click profile MoneyRange.click
click audit MoneyRange.click
click expand --claim MoneyRange.contract MoneyRange.click
```

Every sidecar here verifies the same way. To refresh the lock, install the
pinned C++ front end (`click add cpp`, Linux x86-64 or macOS arm64; in a
checkout, or on another host,
`CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"` instead) and lock the
project; any pinned exporter writes the committed lock and artifacts:

```sh
click capture
```

The lock binds the unit's arguments, exact source and header bytes, all
textual headers Clang opened (the Clang resource headers by digest), exporter,
and observed semantic profile. The exporter supplies the pinned Clang's
resource directory itself, so the project names no machine-specific path. Once
locked, verification loads the artifacts offline without invoking Clang.

## Full checkout

The hermetic closure was cut from a full checkout. Put the unmodified checkout
at `inputs/bitcoin-src`, the extracted development packages at
`inputs/sysroot`, and use `inputs/bitcoin-build` for the CMake build directory.
From the repository root, generate the compilation database:

```sh
cmake -S integrations/bitcoin-core-money-range/inputs/bitcoin-src \
  -B integrations/bitcoin-core-money-range/inputs/bitcoin-build \
  -DCMAKE_TOOLCHAIN_FILE="$PWD/integrations/bitcoin-core-money-range/linux-x86_64-clang19.cmake" \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DBoost_DIR="$PWD/integrations/bitcoin-core-money-range/inputs/sysroot/usr/lib/x86_64-linux-gnu/cmake/Boost-1.74.0" \
  -Dboost_headers_DIR="$PWD/integrations/bitcoin-core-money-range/inputs/sysroot/usr/lib/x86_64-linux-gnu/cmake/boost_headers-1.74.0" \
  -DBUILD_BITCOIN_BIN=OFF -DBUILD_DAEMON=OFF -DBUILD_CLI=OFF \
  -DBUILD_TX=OFF -DBUILD_UTIL=OFF -DBUILD_TESTS=OFF -DBUILD_BENCH=OFF \
  -DBUILD_GUI=OFF -DBUILD_KERNEL_LIB=OFF -DBUILD_UTIL_CHAINSTATE=OFF \
  -DENABLE_WALLET=OFF -DENABLE_IPC=OFF -DWITH_ZMQ=OFF
```

The generated `compile_commands.json` must contain one
`src/policy/feerate.cpp` command with `--target=x86_64-unknown-linux-gnu`,
`-std=c++20`, and no verifier-specific exception or RTTI overrides. The
toolchain file supplies the Linux sysroot, standard-library include paths, and
Clang resource directory needed by the compiler driver.
The sysroot is parse-only input: Clang needs it to type-check Bitcoin Core,
but a function declared in its headers is never exported or verified. Calls
into it are checked against Click's standard-library contracts; see
[the C++ standard library](../../docs/reference/cli/capture.md#c-standard-library).
Some CMake link probes warn because this header-only setup does not install a
Linux runtime; successful configuration and the selected compile command, not
a binary build, are the setup requirements.

## Hermetic gate fixture

The normal `scripts/check.sh` gate also re-exports and verifies this same
`MoneyRange` sidecar without a network or a local Bitcoin checkout. Its
[`input-closure.tar.gz`](input-closure.tar.gz) contains only the 15 Bitcoin
files and 292 Linux sysroot headers observed by the pinned import, plus source
and package notices. The Bitcoin bytes were checked against the exact v31.1
Git tree; every sysroot header was matched to a member of one of the five
SHA-256-pinned Debian packages above. The gate checks the archive digest,
the unchanged selected header and translation unit, the 320-file Clang input
inventory, and re-runs semantic export and proof verification with Clang
19.1.7. No hand-copied function or precomputed semantic artifact is used.

[`feerate-command.json.in`](feerate-command.json.in) is the selected command
from the real Bitcoin CMake-generated compilation database, with only the
checkout/build/sysroot paths and pinned Clang executable/resource paths
relocated for the test machine. [`fixture-manifest.json`](fixture-manifest.json)
records the release commit, original database and import-lock identities,
archive digest, and source, package, and originating Clang executable hashes.
The gate does not rerun Bitcoin's whole CMake configuration; that remains the
opt-in full-checkout workflow above. It also does not build or run Bitcoin.

To regenerate the hermetic fixture, put the full checkout at `bitcoin-src/` and
the extracted packages at `sysroot/` beside the sidecars, in place of the
closure, and lock the project as above. Put the five downloaded `.deb`
archives in `inputs/packages` under the short names shown in the table (for
example `libc6-dev.deb`), then run:

```sh
python3 integrations/bitcoin-core-money-range/make-fixture.py \
  --bitcoin-src integrations/bitcoin-core-money-range/bitcoin-src \
  --sysroot integrations/bitcoin-core-money-range/sysroot \
  --packages integrations/bitcoin-core-money-range/inputs/packages \
  --lock integrations/bitcoin-core-money-range/.click/captures/manifest.json \
  --compilation-database integrations/bitcoin-core-money-range/inputs/bitcoin-build/compile_commands.json
```

Regeneration checks the Git tree, local source bytes, Debian archives and
extracted header bytes, originating Clang executable, the selected compile
flags, and that the `bitcoin` unit states exactly that command, before
changing the checked-in closure. A changed archive also requires
deliberately updating the pinned digest in the gate test after review.

The sidecar proves the exact Boolean range result for every input while
preserving the reference's owned cell. The contract covers `-1`, `0`,
`MAX_MONEY`, and `MAX_MONEY + 1` without separate boundary execution theorems.

The gate also rejects an exclusive upper-bound claim against the unchanged
upstream function. It refuses to load the locked artifact after changes to
`amount.h`, a transitive Linux header, the CMake compile command, or the
configured profile. Selecting `MoneyRange` from a different upstream header
fails refresh, and that rejected selector cannot load the old artifact.

The gate profiles the complete upstream proof and audits all six source
smart-tactic sites. Profile events may also include generated execution steps;
source positions come from the source-site inventory. Each site is
expanded against the same locked import, the resulting certificate is checked
by ordinary verification and a retained audit session, and the expanded
claim has fewer smart sites. The exact range contract covers both endpoints
and out-of-range values without invoking Clang during verification or expansion.

This is one function under one Clang profile, not general Bitcoin Core or
Linux binary verification.

## FeeFrac value methods

The same unchanged input closure and real `feerate.cpp` compilation command
also select `FeeFrac::IsEmpty()`, `FeeFrac::operator+=`, and `FeeFrac::operator-=` from
`src/util/feefrac.h`. Its SHA-256 is
`213a97d13eb82b34831466febcff24f4c20879603f36fc6edd894b89000f7ab9`.
No Bitcoin source, archive contents, or compiler flags were changed for these
proofs. The gate checks the existing archive digest, header digest, and the
320-file Clang inventory before verifying all five sidecars:

- `FeeFracIsEmpty.click` proves the result is exactly `size == 0`, preserving
  both fields, without requiring the application's fee/size invariant.
- `FeeFracAdd.click` proves exact addition for distinct owned objects and
  preservation of the other object's fields. Each input field is bounded to
  half its signed range, sufficient to keep both sums defined.
- `FeeFracAddSelf.click` proves the alias case `self == other`, owning each
  field once and doubling it under the same half-range bounds.
- `FeeFracSubtract.click` proves exact subtraction for distinct owned objects
  and preserves the other object's fields, under the half-range input bounds.
- `FeeFracSubtractSelf.click` proves both fields become zero for `self == other`
  over their entire signed ranges, owning each field once without range bounds.

After the full-checkout setup above, lock and verify each of these sidecars
with the same commands used for `MoneyRange`. Their adjacent import configs
select the exact upstream method; their heads are the C++ declarations,
`bool FeeFrac::IsEmpty() const` and `void FeeFrac::operator+=(const FeeFrac& other)`.
Exceptions and RTTI remain enabled in the real command. Unselected templates,
constructors, wide-integer helpers, and other methods do not enter the proof
graph; the whole record layout and selected method bodies do.

The [synthetic value-method fixtures](../../tests/fixtures/cpp-verification/value-methods/)
separately verify source callers using both `value += value` and
`value.operator+=(value)`, with an unrelated owned cell framed unchanged.
They also check expansion/reverification and retained audit sessions, and
reject false results, incorrect sums, missing field authority, and missing
overflow bounds. Artifact regressions reject const-receiver writes and
const-to-mutable argument conversion independently of Clang's source checks.

These are bounded value-method proofs, not verification of all `FeeFrac`, fee
rounding, `CFeeRate`, or Bitcoin Core.

The [subtraction caller fixture](../../tests/fixtures/cpp-verification/subtract-methods/)
checks that self-subtraction preserves unrelated caller memory. The
[signed arithmetic fixtures](../../tests/fixtures/cpp-verification/signed-arithmetic/)
check quotient/remainder contracts, overflow and zero-divisor rejection, C++20
signed narrowing and Boolean conversion, and Bitcoin's correction expression
for concrete rounding cases with a signed 64-bit dividend. They do not prove
upstream `FeeFrac::Div` or `EvaluateFeeDown/Up`: this pinned compiler profile
uses `__int128` for the former and a templated unsigned fast path for the latter.


## Wide fee product

[`FeeFracMul.click`](FeeFracMul.click) selects the unchanged `FeeFrac::Mul`
from the same v31.1 header, archive, and x86-64 Linux compilation command.
Its header SHA-256 remains
`213a97d13eb82b34831466febcff24f4c20879603f36fc6edd894b89000f7ab9`.
The actual body is `return __int128{a} * b;`; the wide path is selected by
`__SIZEOF_INT128__`, with no fallback or source rewrite.

The sidecar explicitly states the complete signed 64-bit and 32-bit observer
ranges. Two `integer_product_bounds` certificates then establish the native
128-bit product bounds before execution. The result equals the exact
mathematical product `to_integer(a) * to_integer(b)`, rather than the
potentially overflowing narrow machine expression `to_integer(a * b)`.
These requirements cover the full input ranges; the proof currently states
those type bounds instead of inferring them automatically.

The hermetic gate checks the 320-file closure, fresh semantic export, ordinary
verification, expansion/reverification, and retained audit. It rejects false
products, missing named bounds, and execution without native product bounds.
The [synthetic modular caller](../../tests/fixtures/cpp-verification/scalar-braces/braces.cpp)
uses the same helper body and preserves unrelated owned narrow memory.
It is caller-composition coverage, not an added Bitcoin wrapper.

The next selected upstream helper is the unchanged `FeeFrac::Div`:

```cpp
Assume(d > 0);
int64_t quot = n / d;
int32_t mod = n % d;
return quot + ((mod > 0) - (mod && round_down));
```

The missing-contract refusal keeps this source out of the admitted profile.
A consteval-only regression pins `util/check.h` (SHA-256
`82705f6150e57b4de9123d22b3820f60f6f75f58c1c8b9fbff78863afca816a7`)
and admits the real template, Boolean temporary, discarded reference return,
and forced `std::source_location::current()`, then rejects the runtime
string-view argument.

The new `checked_boolean_statement_with_literal_metadata` opt-in regression
imports and lowers the complete unchanged `FeeFrac::Div`. Its separate
`literal_constructor` descriptor names
`std::basic_string_view::basic_string_view` and pins the unchanged sysroot header
`sysroot/usr/include/c++/12/string_view` to SHA-256
`9b1a575ffad1e8575cd6fc1c9a24b0cdde3793275be431726cc9c1b178a8733c`.
The artifact retains `"d > 0"`, the resolved `std::basic_string_view<char>` type,
by-value binding, and constructor origin. The source, archive, 320-file
closure, and real compiler command remain unchanged.

Bitcoin's `Assume` expands to `inline_assertion_check<false>` in `util/check.h`,
with source-location and string-view arguments and a build-dependent abort
policy. It is an evaluated library call, separate from Clang's unevaluated
`__builtin_assume`. The explicit assertion contract requires proof that the
condition is true and assumes defined normal behavior without caller-visible
memory changes under that condition. The independently pinned constructor
contract assumes defined normal construction from admitted literals without
caller-visible memory changes. Neither library implementation is verified.
Trivial initialization and destruction are checked compiler properties; runtime
pointers, arbitrary conversions and cleanup effects remain rejected.

The integration verifies that a missing condition still fails at the named
library obligation. Plain execution from a positive narrow divisor still
requires the wide nonzero guard. An explicit checked proof now bridges
`1 <= d` to Integer and excludes `0` and `-1` to derive both wide guards
from `d > 0`; it reaches the unbounded narrow correction, including for a
zero numerator observation. These failures remain
bounded and cannot be hidden with a trivial postcondition. The shared arithmetic
foundation now includes explicit quotient/remainder
interval bounds and equality transport. Standalone C++ narrowing proofs derive
their bounds from operand ranges and compose them with exact native observations
and checked cast identities; they are pattern coverage, not a proof of this
Bitcoin helper. Native int32/int64 comparisons in specifications read as
Integer comparisons, so standalone checked narrowing proofs compose proved
Integer bounds directly with cast identities and preserve a modular caller's
unrelated memory.

[`FeeFracDivBounded.click`](FeeFracDivBounded.click) now proves complete
execution safety and both Integer/native output bounds of the unchanged pinned
helper. Its joint input bounds are
`INT64_MIN * d <= n <= INT64_MAX * d`, with `0 < d <= 2147483647`.
This admits every positive int32 divisor, int128 numerators far outside int64,
and exact division at both int64 endpoints. For either value of `round_down`,
the result lies in the full native range `[INT64_MIN, INT64_MAX]`.

Both narrowing identities are derived from quotient/remainder intervals. The
remainder interval uses the divisor's maximum magnitude, so it stays inside
int32 even for the wider numerator range. A positive remainder excludes
`INT64_MAX` for the quotient, and a negative
remainder excludes `INT64_MIN`: reconstruction would otherwise contradict the
scaled input bound. Shared proof-backed `integer::upper_correction_bound` and
`integer::lower_correction_bound` lemmas establish one unit of margin only in
the relevant branch. After proving native definedness there, `close()` states
each possible corrected sum's exact Integer value, which bounds it; the native
result bounds are those Integer comparisons, read directly. No output range is
assumed. The sidecar retains the explicit pinned
library assumptions described above.

Full proof expansion reverifies; retained audit and hostile omitted input
bounds, zero divisor, false result claims and swapped cast-certificate references
have coverage. The standalone fixture retains the same correction pattern and
verifies native output bounds and unrelated memory through a modular caller.
The sidecar also proves the exact corrected quotient in each remainder-sign
case, including zero, and the defining mathematical product inequalities:

- Floor (`round_down == true`): `result * d <= n < (result + 1) * d`.
- Ceiling (`round_down == false`): `(result - 1) * d < n <= result * d`.

These specifications use `to_integer` observations and Integer arithmetic, so
their products and successor/predecessor expressions have no native overflow.
The shared proof-backed `integer::floor_from_remainder` and
`integer::ceiling_from_remainder` lemmas combine reconstruction, positive-divisor
remainder bounds and exact correction values. Explicit Integer distributivity
connects the corrected product; affine certificates keep complete nonlinear
terms opaque. The modular caller exports the same four inequalities and frames
untouched memory. Strict claims that fail on exact division are rejected.

This completes mathematical rounding on the stated joint bounded profile.
The wide-fallback `EvaluateFeeDown/Up` composition and both unsigned fast paths
are verified below, along with unified callers on the joint input profile.
The alternative result-fit profiles below widen the helper's mode-specific
numerator domain. Fee callers still use the joint profile.

## Mode-specific fee division result fit

[`FeeFracDivResultFitDown.click`](FeeFracDivResultFitDown.click) and
[`FeeFracDivResultFitUp.click`](FeeFracDivResultFitUp.click) verify the same
unchanged `FeeFrac::Div` source under separate contracts. Select the profile
for the required rounding mode; these sidecars are alternatives to the joint
helper contract, rather than declarations to load together.

With `N = to_integer(n)`, `D = to_integer(d)`, `MIN = INT64_MIN` and
`MAX = INT64_MAX`, both require a positive int32 divisor and explicit native
`d <= INT32_MAX`. Down requires `round_down == true` and
`MIN * D <= N < (MAX + 1) * D`. Up requires `round_down == false` and
`(MIN - 1) * D < N <= MAX * D`. For `D > 1`, Down includes positive
numerators above `MAX * D`; Up includes negative numerators below `MIN * D`.
For example, with `D = 2`, Down accepts `2 * MAX + 1` and returns `MAX`,
while Up accepts `2 * MIN - 1` and returns `MIN`.

Each proof derives the int64 truncating quotient bounds using the shared
strict quotient lemmas on its widened side, checks the actual native division
and both casts, and establishes int32 remainder bounds. Down proves decrement
safety only for a negative remainder; Up proves increment safety only for a
positive remainder. The source still performs its original mode-dependent
correction. Both contracts export native and observer result bounds, exact
remainder-sign correction identities, and unguarded floor/ceiling inequalities
for the selected mode. No C++ source, importer or kernel change is needed.

Eight hermetic phases cover ordinary verification, source expansion and
reverification, retained verification, missing mode/divisor/numerator guards,
strict endpoints weakened to inclusive ones, false rounding inequalities,
missing correction bounds and reversed cast evidence. The original callers retain the joint contract. The alternative wide caller
profiles below compose these mode-specific interfaces with larger amounts.

## CompactSize encoded length

The same pinned v31.1 archive and unchanged `feerate.cpp` compilation command
select `GetSizeOfCompactSize` in `src/serialize.h` (SHA-256
`87a273aa8cb9aeea82cd8038bb85284a5782c8abc35f8c826eb60f1a01e06775`).
The 320-file input closure and compiler flags remain unchanged. Four sidecars
cover all uint64 values:

| Sidecar | Input range | Encoded length |
| --- | --- | --- |
| `CompactSize1.click` | 0 through 252 | 1 byte |
| `CompactSize3.click` | 253 through 65,535 | 3 bytes |
| `CompactSize5.click` | 65,536 through 4,294,967,295 | 5 bytes |
| `CompactSize9.click` | 4,294,967,296 through UINT64_MAX | 9 bytes |

Use the same lock/verify setup described above. Their configs pin unsigned
`uint64_t` aliases to `bits/stdint-uintn.h` and `bits/types.h` in the hermetic
sysroot. Pinned Clang evaluates the helper's `sizeof` and constexpr
`std::numeric_limits::max()` expressions; artifacts retain their source spans
as distinct compiler constants and lock the entire preprocessor input closure.
This is part of the compiler trust boundary, not a standard-library proof.
The gate checks ordinary verification, expansion/reverification, retained audit,
and false length claims for each range. It does not prove serialization bytes,
parsing, or round trips.


The hermetic gate now also selects the unchanged `FeeFrac::EvaluateFeeDown`
and `EvaluateFeeUp` entry points. Export retains each compiler-resolved Boolean
template instance and both wide helpers, rather than removing the fallback.
Bitcoin's evaluated `Assume(size > 0)` reads its receiver field under ordinary
memory authority; its header and literal constructor remain explicitly pinned.
`[[likely]]` preserves both branch outcomes. The gate combines the existing
verified Mul/Div sidecars with concrete caller contracts: fee 7, size 3 and
at_size 2 return 4 downward and 5 upward, preserving both receiver fields.
It checks ordinary verification, caller expansion/reverification, and rejection
of false results, missing field authority and missing size/amount premises.
These concrete fast-path claims remain source admission regressions.

[`FeeFracEvaluateWide.click.in`](FeeFracEvaluateWide.click.in) now supplies
symbolic caller contracts for negative fees and positive fees at least `2^33`
on the unchanged wide fallback.
The hermetic tests instantiate its native branch guard, Down/Up mode and
product inequalities, then compose it with the existing verified Mul and Div sidecars in one prepared
project. It is a caller template, rather than a standalone sidecar with assumed
helpers; the same run proves the actual helper bodies and both caller levels.

The contract explicitly requires field `views`, a native fee below zero or at
least `2^33`, its full int64 observer bounds, positive int32 size and `0 <= at_size <= size`.
Both modes preserve fee and size and prove full int64 result observer bounds.
Writing `F`, `A`, `D` and `R` for the Integer observations of fee, amount, size
and result, Down proves `R * D <= F * A < (R + 1) * D`; Up proves
`(R - 1) * D < F * A <= R * D`. These include zero amount and signed endpoints.
Existing proof bindings name the captured denominator and the Mul/Div results;
explicit Integer equality rewrites connect their bounds to the caller claim.
The template does not mention generated C++ temporary names.

The gate verifies the unchanged compiler-selected graph, expands both the
wrapper and template-instance proof, reverifies the rewrites, checks retained
verification, and rejects missing authority/domain bounds, forged Mul product
equalities and false rounding inequalities. The evaluated `Assume` contract
and compiler/library pins remain the profile described above.

The shared uint64 Integer lemmas provide exact no-wrap multiplication and
nonzero division/remainder; `close()` states the in-range addition and
subtraction identities, and native comparisons read as Integer ones. The
checked contracts and ordinary C regressions are described in [the Integer model](../../docs/internals/mathematical-integers.md#exact-unsigned-64-bit-observations).
The cast certificate now also recognizes the legacy 32/64-bit terms of the
fast-path operand conversions, using the same typed modulo policy and explicit
source bounds. The symbolic uint64 return-to-int64 conversion is admitted only
with a proved native INT64_MAX upper bound. Ordinary C modular regressions and
the checked [cast fixture](../../mdtests/legacy_integer_cast_identity.md) cover
these shared prerequisites.

[`FeeFracEvaluateFastDown.click.in`](FeeFracEvaluateFastDown.click.in) verifies
the unchanged unsigned Down fast path for symbolic fees from zero through
`2^33 - 1`, positive int32 size and `0 <= at_size <= size`. Both the wrapper and
Boolean template instance preserve the fields, prove `0 <= R <= 2^33 - 1`,
establish `R == truncating_quotient(F * A, D)`, and prove the floor inequalities
`R * D <= F * A < (R + 1) * D`. Native branch guards and fee observer bounds
are explicit prerequisites; result representability is derived.

The proof checks each mixed-width cast, uses the scaled-product bound to
exclude uint64 multiplication wrap, excludes zero in both divisor domains,
and transports exact division into Integer arithmetic. Quotient bounds prove
the native INT64_MAX guard for the source's signed return. Integer reconstruction
and nonnegative remainder bounds establish floor rounding. It uses the same
pinned compiler graph, evaluated Assume profile and verified helper sidecars;
the Bitcoin implementation is unchanged.
The gate expands and reverifies both caller levels, checks retained verification,
and rejects missing field/domain/fee bounds and false quotient or strict rounding
claims. Zero fee, zero amount, exact division and maximal fast-path fee/size
are included in the symbolic domain.

[`FeeFracEvaluateFastUp.click.in`](FeeFracEvaluateFastUp.click.in) proves the
unsigned Up fast path on the same symbolic domain, including both caller levels.
It establishes `R == truncating_quotient(F * A + D - 1, D)`,
`0 <= R <= 2^33 - 1`, and the ceiling inequalities
`(R - 1) * D < F * A <= R * D`, preserving the fields.

The mixed-width casts remain explicit. The proof separately checks that the
source's uint64 product-plus-size cannot wrap and that subtracting one cannot
underflow, then transports the exact shifted numerator to Integer arithmetic.
A loose quotient bound first justifies the checked signed return; reconstruction,
remainder bounds and multiplication order sharpen the result bound and prove
ceiling rounding. The same helper bodies and pinned compiler/library profile
are verified in the prepared project. The gate checks wrapper/instance expansion,
reverification and retained verification, and refuses missing domain/fee bounds,
missing numerator identities, forged shifted identities and false quotient/rounding.

Separate contracts cover both modes in the negative, unsigned-fast and
positive-wide fee domains under the joint amount/size bounds. The unified caller
contract below combines them; the alternative wide result-fit profiles follow.

[`FeeFracEvaluateBounded.click.in`](FeeFracEvaluateBounded.click.in) unifies the
three domains for Down and Up without a native fee-branch prerequisite. It
requires full int64 fee observer bounds, positive int32 size, field views and
`0 <= at_size <= size`. Both caller levels preserve fields, prove int64 result
bounds and the corresponding floor/ceiling product inequalities for every fee.
The hermetic factory reuses the existing verified helper and branch proof
fragments, supplying distinct captures for the two wide branches. Bitcoin's
source guards `fee >= 0` and `fee < 2^33`, read as Integer comparisons, derive
the fast-path range. Expansion/reverification, retained verification and
missing-bound, false-rounding and missing-transport regressions cover both modes.
Shared strict quotient lemmas now establish initial int64 quotient fit on
floor's `MIN * d <= n < (MAX + 1) * d` and ceiling's
`(MIN - 1) * d < n <= MAX * d` mathematical domains; see
[`integer_quotient_strict_bound.md`](../../mdtests/integer_quotient_strict_bound.md).
The mode-specific helper profiles above prove native narrowing and correction
on these domains. The wide callers below now compose those helper contracts.


## Wide fee callers with explicit result fit

[`FeeFracEvaluateWideResultFit.click.in`](FeeFracEvaluateWideResultFit.click.in)
verifies Down and Up on both wide fallback domains: negative fees, and
nonnegative fees at or above the source's `2^33` fast-path threshold. The
hermetic factory supplies the selected mode's Div sidecar and the unchanged
Mul sidecar in the same prepared project. These alternative caller profiles
preserve the actual source guards; they do not cover the unsigned fast path.

Both caller levels require field views, full signed fee observer bounds,
positive int32 size, and `0 <= at_size <= INT32_MAX`. With `F`, `A`, `D`
the Integer observations of fee, amount and size, Down requires
`MIN * D <= F * A < (MAX + 1) * D`; Up requires
`(MIN - 1) * D < F * A <= MAX * D`. There is no `at_size <= size`
prerequisite. Native multiplication is checked by the Mul sidecar, and explicit
rewrites transport its exact product identity to the selected Div contract.
The callers derive signed result bounds and exact floor/ceiling inequalities,
and preserve both fields.

Each of the four profiles includes a modular execution example with fee
`2^33` or `-2^33`, size `1`, and amount `2`. Its contract explicitly states the
same fit/authority premises and the fixed inputs, and exports the rounding
intervals and field frames. This makes `at_size > size` a checked contract
application, rather than only an example mentioned in prose.

Sixteen hermetic phases cover ordinary, wrapper/instance expansion and retained
verification, missing field/size/amount/product guards, strict input endpoints
weakened to inclusive ones, omitted wide-branch or fee bounds, forged product
transport and false rounding. Original wide, fast and unified joint-bound
profiles remain separate regressions. The unsigned fast profiles below now use
these amount/result-fit bounds; the broader unified profiles follow below.


## Unsigned fast fee callers with explicit result fit

[`FeeFracEvaluateFastResultFitDown.click.in`](FeeFracEvaluateFastResultFitDown.click.in)
and [`FeeFracEvaluateFastResultFitUp.click.in`](FeeFracEvaluateFastResultFitUp.click.in)
verify the unchanged unsigned fast path with `0 <= at_size <= INT32_MAX` and
positive int32 size. They retain the source's native nonnegative fee and
`fee < 2^33` guards, explicit fee observer bounds `0 <= F <= 2^33 - 1`,
and field views. Down requires `F * A < (INT64_MAX + 1) * D`; Up requires
`F * A <= INT64_MAX * D`. The lower signed-fit bound is automatic on this
nonnegative domain. Neither profile requires `at_size <= size`, and the
result bound is now `0 <= result <= INT64_MAX`, rather than a fee-sized bound.

Explicit rectangular product certificates give
`0 <= F * A <= 18446744062972133377` from the fee/amount ranges, independently
of `D`. This checks the uint64 multiplication. Up also checks the actual
`product + size` addition and subtraction of one, including the lower bound
that prevents unsigned underflow. Down applies the shared strict scaled
quotient upper bound to the product. Up derives
`F * A + D - 1 < (INT64_MAX + 1) * D` from its fit premise and applies the
same quotient bound to that adjusted numerator. Both reflect the derived
quotient limit back to native uint64 order before the ordinary int64 return
cast, and check the cast's observer identity.

Both caller levels preserve fields, export exact floor/ceiling product
inequalities, and identify the result with the corresponding truncating
quotient of the actual native numerator. Four modular examples cover fee 7,
size 1, amount 2, and the maximum fast fee/native amount with size 2. The latter
uses a uint64 product above `INT64_MAX`, while the rounded result still fits.

Twelve bounded hermetic phases cover ordinary, wrapper/instance expansion and
retained verification, omitted authority/amount/result-fit/fee/branch guards,
relaxed result-fit bounds, false rounding, missing product/division bridges,
and Up's missing addition/subtraction or forged adjusted numerator. The wider
fast and wide profiles remain available separately; the unified profiles below
compose them under the broader product-fit domain.


## Unified fee callers with explicit result fit

[`FeeFracEvaluateResultFit.click.in`](FeeFracEvaluateResultFit.click.in) combines
all three source branches under one contract per rounding mode. Both caller
levels require field views, full int64 fee observer bounds, positive int32
size, and `0 <= at_size <= INT32_MAX`. For Integer observations `F`, `A`, `D`,
Down requires `MIN * D <= F * A < (MAX + 1) * D`; Up requires
`(MIN - 1) * D < F * A <= MAX * D`. There is no fee-branch prerequisite or
`at_size <= size` requirement. The contracts export int64 result bounds, exact
floor/ceiling product intervals, and both field frames.

The hermetic factory reuses the wider fast and fallback proof bodies and the
selected mode's Div sidecar, alongside the unchanged Mul sidecar. Bitcoin's
actual native guards, read as Integer comparisons, derive the fast fee observer
bounds. The two fallback branches have distinct captures. The
fast proof checks uint64 product and adjusted-numerator arithmetic and the
ordinary int64 return cast; the fallback proofs transport the exact int128
product to the selected result-fit Div contract. Bitcoin's implementation,
compiler/library assumptions, importer and kernel are unchanged.

Each mode includes four modular contract applications: fee `7`, size `1`,
amount `2`; fee `2^33 - 1`, size `2`, amount `INT32_MAX`; and fees `2^33` and
`-2^33`, each with size `1` and amount `2`. They state the general authority
and fit premises plus fixed inputs and export the rounding intervals, result
bounds and frames. All source branches are covered, including an unsigned
product above `INT64_MAX` whose quotient fits.

Seventeen bounded hermetic phases cover ordinary verification, wrapper and
instance expansion/reverification, retained verification, missing field,
amount, fee or fit bounds, strict fit endpoints weakened to inclusive ones,
missing source-comparison transport, false rounding, missing arithmetic
identities, and forged wide products or ceiling numerators. The original unified
joint-bound profile remains a regression. The unchanged `CFeeRate::GetFee`
composition below adds inherited `FeePerVSize` field access, empty-rate behavior
and the negative-fee minimum correction to these rounding proofs.


## CFeeRate wrapper preparation

The selected unchanged `CFeeRate::GetFee` implementation adds encapsulation,
header-declared records, nested field access and inherited `FeePerVSize`
receivers to the existing rounding proof. The first prerequisite now supports
named standard-layout classes with the same signed scalar/pointer fields as
structs. Private, protected and default-private fields retain Clang-resolved
declaration identities, offsets and sizes. Clang checks source access control;
proof sidecars use the ordinary field views and ownership required by the
shared C memory model. Const reads do not grant write authority.

The [`class-record` fixture](../../tests/fixtures/cpp-verification/class-record/class_record.cpp)
checks const readers, mutable field updates, frames, expansion/reverification
and retained verification. Hostile claims, omitted authority and writes through
views are rejected, as are illegal C++ client access, unions, mixed-access
non-standard layouts, general inheritance and bit-fields.

The pinned `CFeeRate::GetFee` now imports and verifies its complete unchanged
call graph. Direct Boolean condition calls, executable ordinary callees in
locked headers, inherited receivers and the `CAmount` conversion compose the
observer and arithmetic proofs described below.

## GetFee composition

[`CFeeRateGetFee.click.in`](CFeeRateGetFee.click.in) composes the existing unified
Up result-fit proof with a read-only `IsEmpty` contract. Both nested fields are
viewed and preserved. Amount and stored size are nonnegative int32 values.
For size zero, the result is zero; no fee observer or product-fit premise is
needed. For positive size, write `F`, `A`, `D` for the Integer observations of
fee, amount and size. The caller supplies the full int64 fee observer bounds
and `(MIN - 1) * D < F * A <= MAX * D`, exactly the unified Up profile.

Let `C` be the ceiling of `F * A / D`. The result is `C`, except that `C == 0`,
a nonzero amount and a negative native fee produce `-1`. The sidecar expresses
this exactly with the ceiling interval or the minimum-correction interval
`-D < F * A <= 0`, together with the exclusion of a zero result for nonzero
negative-fee calls. It also exports full int64 result bounds and both field
frames. The `CAmount` conversion introduces no fit assumption.

The shared `IsEmpty` sidecar now uses field views and exports both directions
of its Boolean result. The proof names the ordinary helper results, branches at Bitcoin's `IsEmpty`
condition, and explicitly rewrites the zero rounded value before transporting
its ceiling bounds into the correction interval. It adds no kernel rule,
range inference or source change. Execution-theorem proof blocks also retain
their executed arguments' record type metadata, so their field paths use the
same physical layout as ordinary function proofs. A small independent
regression checks nested fields, expansion, retained certificates, omitted
premises and invalid field names. Bitcoin's `Assume` calls and pinned standard
library constructor remain explicit import assumptions.

Bounded hermetic tests remove the exporter before locked loading and proof
checking. Ordinary verification, expansion/reverification and retained
certificates agree. Modular callers cover an empty rate without fee/fit bounds,
negative minimum-fee inputs, zero amount and positive amount above stored size.
Hostile checks omit either field view, amount/size guards, fee bounds or either
fit endpoint; weaken the strict lower endpoint; falsify empty or correction
results; and change a reachable locked header. The selected Bitcoin sources and
input archive are unchanged.


## GetFeePerK composition

[`CFeeRateGetFeePerK.click.in`](CFeeRateGetFeePerK.click.in) verifies the unchanged
inline header method. It calls `EvaluateFeeDown(1000)` directly, not `GetFee`.
It therefore requires positive stored size and applies neither the empty-rate
branch nor the negative minimum-fee correction. For Integer fee/size observers
`F`, `D`, its fit profile is `MIN * D <= F * 1000 < (MAX + 1) * D`.
The result satisfies `R * D <= F * 1000 < (R + 1) * D`, full int64 bounds, and
both receiver field frames. The proof reuses the unified Down contract and
existing execution rules without a Bitcoin or kernel change.

Hermetic tests remove the exporter before locked verification. Ordinary,
expanded/reverified and retained checks agree. Modular callers cover positive,
negative and zero fees, amount 1000 above stored size, and the wide fee branch.
Missing positive-size, field authority or fit assumptions, an inclusive upper
fit endpoint and false rounding claims are rejected.

Original signed/unsigned 128-bit call-result conversions also use the shared
callee-typed capture and ordered conversion chain. Naming that result lets an
explicit proof transport modular bounds to a checked cast certificate. Both
destination endpoints are required for value preservation; this does not add
automatic observer normalization or infer ranges. Offline initializer/return
regressions cover all signedness combinations and 32/64-bit destinations.


## Record declarations in locked headers

The [`header-record` fixture](../../tests/fixtures/cpp-verification/header-record/header_record.cpp)
keeps a class declaration in `state.h` and const/mutable method definitions in
the selected `.cpp` source. Clang-resolved record and field declarations retain
the header's relative path and source spans, alongside exact declaration IDs
and physical layouts. The same declaration-source mechanism serves existing
scalar aliases; every discovered header must match an explicitly configured,
locked dependency. A field declaration must share its record's source.

The selected function remains in its configured logical source. Reachable
ordinary method/free-function bodies can now come from explicitly locked
headers; each body and its executable/member/callee-use spans stay within one
source. Alias declaration spans may come from the locked declaration inventory.
Every reachable body is validated and requires ordinary verified contracts;
unrelated record declarations are not imported. Dependency-header constructor/destructor
bodies and constant definitions and mixed-source executable spans remain
unsupported. Views and ownership, const receiver rules and the shared
C memory model remain unchanged. Const reads and mutable updates verify
offline after removing the exporter, including expansion/reverification and
retained verification.

Regressions reject missing header dependencies, changed locked header bytes,
forged or mismatched record/field source spans, and executable spans relabeled
as header declarations. Semantic validation is checked even when artifact
file digests are recomputed. Deterministic inventory regressions cover both
selected-source and header origins with work linear in declarations and fields.


## Embedded record declarations and contract fields

The [`nested-record` fixture](../../tests/fixtures/cpp-verification/nested-record/nested_record.cpp)
retains a private embedded record with two fields of the same child record type.
Exact declaration identities, offsets, widths and alignment remain structural;
only the physical copy layout uses C's existing qualified leaf representation.
Nested contract views and ownership use the same C field metadata and memory
model. Const scalar reads and outer scalar updates verify offline, expand and
reverify, and preserve nested field frames under retained verification.

The artifact validator resolves all child declarations before checking extents,
rejects by-value cycles, and checks transitive record reachability. Shared
layouts are visited once by the declaration walk. Materializing physical leaf
layouts is separately bounded to 65,536 leaves across the import. Regressions
reject forged child identities, names, constness, widths, offsets, alignment,
missing declarations, cycles, false sibling frames, missing authority,
read-only writes and excessive shared-layout expansion.

Declaration and contract metadata now also support nested C++ source field
reads, writes, signed compound updates and projected method/reference calls.
Automatic objects with embedded fields and nontrivial embedded destruction
remain explicit boundaries. The unchanged `CFeeRate::GetFee` composition is
verified above.


## Nested source field accesses

The nested-record fixture also reads a signed-64 leaf through a const receiver,
updates a separate child object's signed-64 field through explicit `this`, and
performs a bounded signed-32 compound update. A const reference-parameter reader
uses the same representation. Each access retains its root declaration and an
ordered path of owner/field identities and per-function use spans. A shared
indexed resolver validates those identities and lowers the exact accumulated
byte offset. The root's constness applies to writes through the complete path.
Reading a pointer field through a const object does not make the pointee const;
its separate views/ownership still control reads and writes through that pointer.

Offline ordinary, expanded and retained proofs check leaf authority and sibling
frames. Regressions reject missing or sibling authority, writes through views,
false frames and unproved signed overflow. Recomputed-digest artifacts cannot
launder invalid owners, field IDs/names, path order/depth, declaration-source
spans, read-only roots or projections attached to unsupported plain places.
Deterministic checks bound work by path length independently of sibling count.
Projected calls now pass embedded record receivers and reference arguments, or
signed-32 leaf references, at their exact byte addresses. Root constness controls
mutable binding even when the projected field declaration is mutable. Modular
callee contracts require authority for that leaf; caller proofs retain sibling
frames. Ordinary, expanded and retained offline checks cover const/mutable child
methods and record/scalar helper references. Hostile contracts and recomputed
artifacts reject missing authority, false frames, wrong targets and const roots
passed to mutable callees. Reference resolution shares the indexed path walk.
Concrete class-template instances now retain their nominal identity, including
empty tags such as `VSizeTag`. Public non-virtual single bases of data-free
trivial wrappers now retain a separate nominal base layout, exposed as `base`
in sidecars. Base fields are not copied into the derived declaration, and
validation rejects forged edges, layouts and cycles. Inherited source reads/writes and
implicit method/reference receivers now use
ordered nominal base projections, including mixed field/base paths. Root
constness and sibling authority are retained. Direct Boolean condition calls now normalize once before branching;
locked-header ordinary executable calls now retain per-function source origin.
Scalar-call result conversions preserve the callee type before the wrapper's
`CAmount` alias conversion. The composition proof above uses these features.

### SpanReader exception propagation

`SpanReaderIgnore.cpp` is a fixture harness that includes the unchanged
Bitcoin `streams.h` at the same v31.1 commit. `SpanReaderIgnore.click` states
both outcomes of `SpanReader::ignore` and its modular caller, without a
precondition excluding malformed input. Success advances the descriptor;
failure throws exactly the opaque `std::ios_base::failure` and leaves the
descriptor unchanged. The caller receives its borrowed memory on either exit.

`streams-input-supplement.tar.gz` adds only the missing original Bitcoin,
libstdc++ and Clang resource headers. It leaves `input-closure.tar.gz`
unchanged. `streams-input-manifest.json` pins each supplemental file and
both archives. The extra libstdc++ header comes from the same SHA-256-pinned
Debian package as the original fixture. Clang's resource headers are relocated
inside the dependency root so `size_t` retains its actual declaration identity
and a locked declaration span. `SpanReaderIgnore-command.json.in` keeps the
original target and semantic flags while selecting the pinned headers explicitly
with `-nostdinc` and system include paths, avoiding two copies of Clang's
`include_next` headers in one search chain. Their license is in `clang-resource.copyright`.
`make-streams-fixture.py` regenerates the
supplement from the pinned checkout, Debian package and Clang resources.

The selected `ios_failure` profile explicitly assumes allocation failure
terminates and trusts the pinned standard exception construction and runtime
storage/destruction. It exposes no message or class layout.

`SpanReaderRead.click` uses the same offline inputs to verify the unchanged
`SpanReader::read`. The source view supplies initialized bytes. On success the
proof checks that every destination byte is initialized and equals the
corresponding entry source byte. It also checks the cursor's pointer and length
after advancing. On short input the proof checks the exact exception and the
unchanged cursor. The test authenticates the `memcpy` declaration, then
verifies the sidecar and replays its expansion both cold and in a retained
session.

`SpanReaderRead32.click` composes that contract with the pinned
`ser_readdata32<SpanReader>` instantiation. Success advances the cursor four
bytes and returns their little-endian value on x86-64. Short input propagates
`std::ios_base::failure` and leaves the cursor unchanged. Typed catches are
tracked in [the exceptions roadmap](../../roadmap/cpp-exceptions.md).
