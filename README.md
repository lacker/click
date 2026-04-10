# click

`click` is a small experimental kernel for the Click language.

The current prototype is intentionally narrow. It has:

- top-level `def`, `check`, and `theorem` declarations
- `Type`
- `Bool`
- `Nil`
- `record-type`
- `sum-type`
- `arrow`
- `record`
- `variant`
- `get`
- `with`
- `has`
- `if`
- `var`
- `app`
- `lambda`
- `nil`
- `true`
- `false`

The reader parses surface S-expressions, then the kernel immediately lowers
them into an internal `Term` language. In that language, values are referred to
by `Name` and record fields or sum tags are selected by `Symbol`. `Term` is opaque rather
than a public enum so the kernel can change its internal representation without
exposing that structure directly.

The structural kernel API is intended to stay in terms of kernel objects.
Constructors and kernel operations should take `Term`, `Name`, `Symbol`,
`Fields`, and `NameMap` rather than host closures or raw Rust strings or
integers. `Context`, `Declaration`, and `run_source` are top-level wrappers
around that smaller kernel.

## Current Semantics

- Ordinary symbols do not self-evaluate. Only `nil`, `true`, and `false` do.
- Top-level `(def name expr)` extends the context for later forms.
- Top-level `(check actual expected)` evaluates both terms and requires exact
  equality.
- Top-level `(theorem name actual expected)` performs the same check, then
  binds the checked term to `name`.
- `record` builds an immutable labeled product.
- `with` returns an updated record.
- `get` projects a record field.
- `has` checks whether a record field exists.
- `variant` builds a tagged sum inhabitant with an explicit `sum-type`.
- `if` treats only `nil` and `false` as falsey.
- `lambda` binds a fresh `Name`.
- The primitive operational semantics is a single reduction step on `Term`s.
- The Rust API exposes that reduction relation as `step(&NameMap, &Term) ->
  ClickResult<StepResult>`.
- The Rust API also exposes `type_of(&NameMap, &Term) -> ClickResult<Term>`.
- Full evaluation iterates those steps until it reaches a canonical `Term`.
- There is no separate runtime `Value` or `Closure` datatype in the current
  kernel.

`Symbol` and `Name` are different things. `Symbol` is an atomic selector, used
for record fields, sum tags, and surface labels. `Name` refers to a value binding. Click
code cannot inspect the character structure of either.

Typing is explicit in the host API. A `NameMap` assigns terms to names, and
`type_of` interprets that map as a type assignment. `step` interprets a
`NameMap` as a value assignment. Lambdas do not store binder types directly;
their binders are `Name`s, and the map provides the type information.

The current type vocabulary is deliberately small: `Bool`, `Nil`, function
types written as `(arrow A B)`, record types written as `(record-type ...)`,
sum types written as `(sum-type ...)`, and a single universe `Type`.

## Deliberate Omissions

The current kernel does not have `quote`, `car`, `cdr`, `cons`, `atom`, or
`atom_eq`.

That is deliberate. The older quote/list experiments were useful for learning,
but they tied code inspection to ordinary list structure. The current design
keeps `Term` as the real kernel syntax and postpones metaprogramming until
Click has a binder-safe way to inspect terms directly.

See [docs/design.md](/Users/lacker/click/docs/design.md) for the current design
notes.

## Usage

Run an expression directly:

```bash
cargo run -- -e "(app (lambda x (var x)) true)"
```

Run a file:

```bash
cargo run -- path/to/file.cl
```

Pipe a program on stdin:

```bash
printf "(with (record) answer true)\n" | cargo run --
```

Install the binary:

```bash
cargo install --path .
```

`click` ignores a leading `#!...` line in source files.

## Example

```lisp
(def id (lambda x (var x)))
(check (app (var id) true) true)
(theorem truth true true)
(with (record) answer (var truth))
```

This evaluates to:

```lisp
(record (answer true))
```

The Rust API uses `Name` directly for bindings. Surface syntax still uses
symbols, and the reader resolves those into fresh names while lowering.

## Historical Bootstrap

The [bootstrap/](/Users/lacker/click/bootstrap) tree is historical. Those files
record earlier quote/list-based experiments and typed probes. They are kept for
language-design lessons, not because they describe the current kernel
interface.
