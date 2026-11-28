# Magic variables

A magic variable is a name a proof reads without the source declaring it. Each
denotes a real value of the verified program or of its proof: the function's
return value, a loop's pass count, or the iterator a `for` loop advances. The
names are fixed, so a reader learns them once; this page lists them all.

| Name | Denotes | Where it is valid |
|---|---|---|
| `result` | the function's return value | postconditions, and proof steps once the function returns |
| `iterations` | the `Integer` count of passes a loop has completed | that loop's clauses and phases |
| `loop(i).iterations` | that count where loop `i` was left | after loop `i` exits, on a path that left it |
| `iter` | the iterator a Rust `for` loop advances | that loop's clauses and phases |
| `loop(i).iter` | the iterator of Rust loop `i` | anywhere loop `i` is in scope |

## `result`

`result` is the value the function returns. It is available in an `ensures`
clause and, in a proof, once the frontier is at function exit, where
`at(function.exit, ...)` reads the returned state. Inside `old(...)` it is
refused, because the entry state has no return value. See
[program binding references](language/index.md#program-binding-references).

A return expression can be evaluated before cleanup runs. Read the value at
the region that computed it, such as `statement(0).read(0).result` for the
load in a Rust function whose tail expression is `b.value` and whose box
`b` is then dropped. Bare `result` denotes the completed function return.

## `iterations`

Inside a loop's clauses and phases, `iterations` is the mathematical `Integer`
count of completed passes: `0` when the invariants are first checked, and one
more at each back edge. A `break` leaves during a pass, which does not count.
Past the loop, `loop(i).iterations` names the count the exit facts state over.
See [loop transitions](tactics/index.md#loop-transitions).

## `iter`

A Rust `for` loop advances an iterator the source does not name:
`for x in bytes` iterates `bytes.into_iter()`, and `for x in bytes.iter()`
iterates the value `bytes.iter()` returns. Inside that loop's clauses and
phases `iter` is that iterator, and `loop(i).iter` names it elsewhere. A
proof reads it through the iterator type's own Rust methods and fields:

- a slice or array iterator: `iter.len()`, `iter.as_slice()` (a slice) and its
  data pointer `iter.as_slice().as_ptr()`;
- a range `a..b`: `iter.start` and `iter.end`;
- an inclusive range `a..=b`: `iter.start()` and `iter.end()`;
- `chunks_exact`: its library methods, such as `iter.len()`;
- `enumerate`: the inner iterator's `iter.len()`.

In nested loops, bare `iter` is the innermost loop's iterator. See
[Rust](rust.md#slice-iterator-loops) for each iterator's model.

## A source variable with the same name

A magic variable takes precedence over a program variable of the same name in
the places it is valid. The program variable is then written
`program::name`, in every source language. For example, a Rust local named `iterations` is `program::iterations`
inside a loop's clauses, where bare `iterations` is the pass count, and a C
local named `result` is `program::result` in a postcondition
([`a_c_local_named_iterations_is_written_program_iterations.md`](https://github.com/clicklang/click/blob/master/mdtests/a_c_local_named_iterations_is_written_program_iterations.md),
[`design/charon-trial/program-bindings`](https://github.com/clicklang/click/blob/master/design/charon-trial/program-bindings/bindings.click)).
