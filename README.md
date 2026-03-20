# click

`click` is a very small Lisp implemented in Rust.

The first version supports:

- `atom`
- `atom_eq`
- `car`
- `cdr`
- `cons`
- `if`
- `lambda`
- `quote`
- `stack`
- `nil`
- `true`
- `false`

This is an experimental programming core. `lambda` is unary, application is left-associative, and bound values are accessed through `stack`.

## Semantics

- Ordinary symbols do not self-evaluate. Use `quote` to write literal atoms and lists.
- `quote` is mainly for list literals: `(quote (a b c))`
- `lambda` captures the current lexical environment.
- Evaluating `stack` returns the current environment as a list, with the nearest binding first.
- `((lambda (car stack)) 'a)` returns `a`.
- Function values are explicit data of the form `(closure body env)`.
- `atom` returns `true` for atoms, booleans, and `nil`.
- `atom_eq` only accepts atoms.
- `if` treats `false` and `nil` as falsey. Everything else is truthy.
- `car` and `cdr` are partial: applying them to `nil` is an error.
- `cons` builds pairs. Proper lists print as `(a b c)`. Improper lists print as `(a . b)`.

## Usage

Run an expression directly:

```bash
cargo run -- -e "((lambda (car stack)) 'a)"
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

## First Self-Hosted Checker

There is now a very small checker written in `click` itself:

- [examples/closure_shape_check.cl](/Users/lacker/click/examples/closure_shape_check.cl)

It checks whether a value has the shape of a closure, and it can run on an
actual runtime closure produced by `lambda`.

```bash
cargo run -- examples/closure_shape_check.cl
```

That example currently prints `true`.
