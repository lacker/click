# click

`click` is a very small Lisp implemented in Rust.

The first version supports:

- `atom`
- `atom_eq`
- `car`
- `cdr`
- `cons`
- `if`
- `quote`
- `nil`
- `true`
- `false`

There is no `lambda`, no function definition, and no user environment yet.

## Semantics

- Ordinary symbols do not self-evaluate. Use `quote` to write literal atoms and lists.
- `quote` is mainly for list literals: `(quote (a b c))`
- `atom` returns `true` for atoms, booleans, and `nil`.
- `atom_eq` only accepts atoms.
- `if` treats `false` and `nil` as falsey. Everything else is truthy.
- `car` and `cdr` are partial: applying them to `nil` is an error.
- `cons` builds pairs. Proper lists print as `(a b c)`. Improper lists print as `(a . b)`.

## Usage

Run an expression directly:

```bash
cargo run -- -e "(cons 'a (quote (b c)))"
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
