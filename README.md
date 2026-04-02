# click

`click` is a very small Lisp-y kernel implemented in Rust.

The current prototype supports:

- `quote`
- `if`
- `atom`
- `atom_eq`
- `car`
- `cdr`
- `cons`
- `var`
- `app`
- `lambda`
- `nil`
- `true`
- `false`

This version uses explicit named variables. Executable list forms are tagged by
their first atom, variable references are written as `(var name)`, and function
application is written as `(app f a)`.

## Semantics

- Ordinary atoms do not self-evaluate. Only `nil`, `true`, and `false` do.
- `quote` turns code into ordinary list data: `(quote (lambda x (var x)))`.
- `lambda` has the form `(lambda x body)` and captures the current lexical environment.
- Rebinding a name that is already in scope is an error.
- Closures are an internal evaluator detail. Evaluating a lambda prints `#<closure>`.
- `atom` returns `true` for atoms, booleans, and `nil`.
- `atom_eq` only accepts atom arguments.
- `if` treats `false` and `nil` as falsey. Everything else is truthy.
- `car` and `cdr` are partial: applying them to `nil` is an error.
- `cons` builds pairs. Proper lists print as `(a b c)`. Improper lists print as `(a . b)`.

## Usage

Run an expression directly:

```bash
cargo run -- -e "(app (lambda x (var x)) 'a)"
```

Run a file:

```bash
cargo run -- examples/list.cl
```

Pipe a program on stdin:

```bash
printf "(car (quote (a b c)))\n" | cargo run --
```

Install the binary and use it as a shebang interpreter:

```bash
cargo install --path .
chmod +x examples/list.cl
./examples/list.cl
```

`click` ignores a leading `#!...` line in source files.

## Code As Data

Quoted code is ordinary data, so Click programs can inspect Click programs with
the usual list operations. For a tiny example:

- [`examples/code_shape.cl`](examples/code_shape.cl) extracts the binder from a quoted lambda.

The larger self-hosted experiments now live in:

- [`bootstrap/README.md`](bootstrap/README.md)
- [`bootstrap/base/fix.cl`](bootstrap/base/fix.cl)
- [`bootstrap/base/assoc.cl`](bootstrap/base/assoc.cl)
- [`bootstrap/base/equal.cl`](bootstrap/base/equal.cl)
- [`bootstrap/data/bool_type.cl`](bootstrap/data/bool_type.cl)
- [`bootstrap/data/bool_true.cl`](bootstrap/data/bool_true.cl)
- [`bootstrap/data/bool_false.cl`](bootstrap/data/bool_false.cl)
- [`bootstrap/data/bool_if.cl`](bootstrap/data/bool_if.cl)
- [`bootstrap/named_core/eval.cl`](bootstrap/named_core/eval.cl)
- [`bootstrap/named_core/wf.cl`](bootstrap/named_core/wf.cl)
- [`bootstrap/token_core/eval.cl`](bootstrap/token_core/eval.cl)
- [`bootstrap/token_core/eval_env.cl`](bootstrap/token_core/eval_env.cl)
- [`bootstrap/token_core/subst.cl`](bootstrap/token_core/subst.cl)
- [`bootstrap/token_core/typecheck.cl`](bootstrap/token_core/typecheck.cl)
- [`bootstrap/token_core/wf.cl`](bootstrap/token_core/wf.cl)

[`tests/bootstrap.rs`](tests/bootstrap.rs) loads those files and checks:

- a recursive assoc-list lookup helper
- a recursive structural equality helper over quoted data
- a first typed `Bool` layer built on the token core
- a self-hosted evaluator for the current named core
- a recursive well-formedness checker for the current named core
- a recursive token-core checker for quoted terms like `(lambda x type (var x))`
- a substitution-based token-core evaluator for closed quoted terms
- a closure/environment-based token-core evaluator for closed quoted terms
- a self-hosted token-core typechecker for quoted terms like `(lambda x type (var x))`

The first typed `Bool` probe already found the practical split: the
substitution evaluator needs alpha-renaming to handle binder collisions, while
the closure/environment evaluator avoids that by carrying environments instead
of rewriting code during evaluation.
