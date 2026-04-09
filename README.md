# click

`click` is a small experimental kernel for the Click language.

The current prototype is intentionally narrow. It has:

- top-level `def`, `check`, and `theorem` declarations
- `object`
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
them into an internal `Term` language. Bound locals are represented internally
with de Bruijn indices. Top-level names stay as atomic `Symbol`s. In the Rust
API, `Term` is opaque rather than a public enum so those lowered locals stay
internal.

The structural kernel API is intended to stay in terms of kernel objects.
Smart constructors may lower internally, but they take `Term`, `Symbol`,
`Object`, `Context`, and `Declaration` rather than host closures or raw de
Bruijn data.

## Current Semantics

- Ordinary symbols do not self-evaluate. Only `nil`, `true`, and `false` do.
- Top-level `(def name expr)` extends the context for later forms.
- Top-level `(check actual expected)` evaluates both terms and requires exact
  equality.
- Top-level `(theorem name actual expected)` performs the same check, then
  binds the checked term to `name`.
- `object` builds an immutable object from symbol keys to canonical terms.
- `with` returns an updated object.
- `get` projects an object field.
- `has` checks whether an object field exists.
- `if` treats only `nil` and `false` as falsey.
- `lambda` binds a scope. Shadowing is allowed.
- The primitive operational semantics is a single reduction step on `Term`s.
- The Rust API exposes that reduction relation as `step(&Context, &Term) ->
  ClickResult<StepResult>`.
- Full evaluation iterates those steps until it reaches a canonical `Term`.
- There is no separate runtime `Value` or `Closure` datatype in the current
  kernel.

Object keys and variable names are symbols, not strings. They are atomic in the
kernel: Click code cannot inspect their character structure.

## Deliberate Omissions

The current kernel does not have `quote`, `car`, `cdr`, `cons`, `atom`, or
`atom_eq`.

That is deliberate. The older quote/list experiments were useful for learning,
but they tied code inspection to ordinary list structure. The current design
keeps `Term` as the real kernel syntax and postpones metaprogramming until
Click has a binder-safe way to inspect terms without exposing raw de Bruijn
indices.

For example, host-side lambda construction uses `Term::lambda(Symbol, Term)`.
That smart constructor captures free occurrences of the given symbol in the
body term, then lowers the result into the hidden de Bruijn core.

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
printf "(with (object) answer true)\n" | cargo run --
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
(with (object) answer (var truth))
```

This evaluates to:

```lisp
(object (answer true))
```

## Historical Bootstrap

The [bootstrap/](/Users/lacker/click/bootstrap) tree is historical. Those files
record earlier quote/list-based experiments and typed probes. They are kept for
language-design lessons, not because they describe the current kernel
interface.
