# click

`click` is a small experimental reflective language core.

The active language is computation-first:

- raw terms are either symbols or objects
- objects are inert data unless they match one of a few executable shapes
- closures, environments, continuations, and evaluator states are ordinary
  objects
- `step` runs over explicit machine states and returns explicit response
  objects

The current executable forms are:

- `:var`
- `:lambda`
- `:apply`
- `:match`
- `:set`

See [docs/design.md](/Users/lacker/click/docs/design.md) for the full design.

## Example

Identity:

```text
(:apply (:function (:lambda (:param :x :body (:var :x))) :arg :ok))
```

This evaluates to:

```text
:ok
```

Matching on a singleton-key object:

```text
(:match
  (:handlers
    (:left (:lambda (:param :x :body (:var :x)))
     :right (:lambda (:param :y :body :wrong)))
   :value
    (:left :payload)))
```

This evaluates to:

```text
:payload
```

## Usage

Run an expression directly:

```bash
cargo run -- -e "(:apply (:function (:lambda (:param :x :body (:var :x))) :arg :ok))"
```

Run a file:

```bash
cargo run -- path/to/file.cl
```

Pipe a program on stdin:

```bash
printf "(:set (:object (:existing :present) :key :answer :value :ok))\n" | cargo run --
```

Install the binary:

```bash
cargo install --path .
```

`click` ignores a leading `#!...` line in source files.

## Rust API

The crate exposes the reflective core directly:

- `Term`, `Object`, and `Symbol`
- `parse` and `parse_many`
- helper constructors such as `var`, `lambda`, `apply`, `match`, and `set`
- `step`
- `eval` and `eval_in_env`
- `run_source` as a host convenience wrapper

## Historical Note

The `bootstrap/` directory is archival. It preserves earlier language-design
experiments, especially quote/list-based and typed-kernel probes, but it does
not describe the active Click language.
