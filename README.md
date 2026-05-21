# click

`click` is a small experimental reflective language core.

The active code is a minimum CEK-kernel demo:

- raw terms are symbols or objects
- expressions are symbols, `:var`, `:lambda`, and `:apply`
- values are symbols and closures
- environments, continuations, states, outcomes, claims, and proofs are ordinary
  objects
- `cek_step` runs one trusted small step over an explicit evaluator state
- `check` validates small-step and many-step claims using proof objects

See [docs/design.md](docs/design.md) for the current design. The human-owned
top of that file is protected; the lower section documents the current kernel
proposal.

## Example

Identity:

```text
(:apply (:function (:lambda (:param :x :body (:var :x))) :arg :ok))
```

This evaluates to:

```text
:ok
```

The same program starts as an explicit CEK state:

```text
(:eval
  (:expr (:apply
    (:function (:lambda (:param :x :body (:var :x)))
     :arg :ok))
   :env ()
   :continuation :halt))
```

One step returns an outcome:

```text
(:next next-state)
(:return value)
(:error info)
```

## Usage

Run an expression directly:

```bash
cargo run -- -e "(:apply (:function (:lambda (:param :x :body (:var :x))) :arg :ok))"
```

Run a file:

```bash
cargo run -- examples/identity.cl
```

Pipe a program on stdin:

```bash
printf "(:apply (:function (:lambda (:param :x :body (:var :x))) :arg :stdin-ok))\n" | cargo run --
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
- expression constructors: `var`, `lambda`, and `apply`
- CEK constructors: `initial_state`, `eval_state`, `continue_state`, `halt`,
  and `closure`
- `cek_step` and `step`
- `eval`, `eval_in_env`, and `run_source`
- claim/proof helpers such as `cek_evals_to_claim`, `cek_next_proof`, and
  `check`
