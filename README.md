# click

`click` is a small experimental reflective language core.

The active code is a kernel object-calculus demo:

- raw objects are symbols or records
- expressions are explicit records such as `:quote`, `:var`, `:lambda`,
  `:apply`, `:get`, `:with`, `:has`, `:equal`, and `:if`
- values are raw objects; closures are ordinary records
- `cek_step` runs one trusted small step over an explicit evaluator state
- `check` validates finite-trace proof objects against claim objects

See [docs/design.md](docs/design.md) for the current design.

## Example

Identity:

```text
(:apply (:function (:lambda (:param :x :body (:var :x))) :arg (:quote :ok)))
```

This evaluates to:

```text
:ok
```

Record access:

```text
(:get (:record (:quote (:answer :ok)) :key :answer))
```

also evaluates to:

```text
:ok
```

## Usage

Run an expression directly:

```bash
cargo run -- -e "(:apply (:function (:lambda (:param :x :body (:var :x))) :arg (:quote :ok)))"
```

Run a file:

```bash
cargo run -- examples/identity.cl
```

Pipe a program on stdin:

```bash
printf "(:get (:record (:quote (:answer :ok)) :key :answer))\n" | cargo run --
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
- expression constructors: `quote`, `var`, `lambda`, `apply`, `get`, `with`,
  `has`, `equal`, and `if_expr`
- CEK constructors: `initial_state`, `eval_state`, `continue_state`, `halt`,
  and `closure`
- `cek_step`, `eval`, `eval_in_env`, and `run_source`
- claim/proof helpers such as `returns_claim`, `returns_next_proof`, and
  `check`
