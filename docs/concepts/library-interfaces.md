# Library interfaces

A library interface is how Click sees a library the verified code calls: the
types it provides, what a value of each type owns, and the contract of each
function. This page states how every library interface is designed, in C, C++
and Rust, and how to add one. Follow it whenever Click gains support for
another standard-library or core function or type.

## Principles

1. **Click defines the interface; the implementation is never used.** A
   library's own code, a C library's bodies, a C++ header's templates or the
   Rust standard library's source, is never imported or verified, and nothing
   Click does depends on how it is written. Each call is checked against the
   Click contract, and that the real library meets the contract is an
   assumption `click verify` reports ([trust](trust.md#library-interfaces)).
2. **State what is observable.** An interface describes a type by its logical
   value (a vector's elements, a box's contents), what its values own, each
   function's preconditions and effects, and what a call invalidates. It never
   names the type's private fields or its representation.
3. **Library types use the mechanisms user types use.** A library type's
   ownership and its functions' contracts are written the way a crate or a C
   program would write its own type's: the same resources and the same
   `extern` contracts. A user's `MyBox<T>` and Rust's `Box<T>` are handled
   alike, so neither the kernel nor a front end knows either one by name.
4. **Language primitives are lowered; library code is called.** A front end
   lowers the language's own primitives directly: C pointers and arrays, Rust
   references and slices, and the steps the compiler builds in, such as `*b`
   on a box. A library function or type gets only an entry in the front end's
   name table, mapping the call to its contract. A front end never rewrites a
   library call into what its implementation does.
5. **When a contract cannot say it, extend contracts.** If a library function
   cannot be stated with today's contracts and resources, the gap is in
   contracts, and its fix is general: every later interface gets it too. Do
   not add a front-end special case; report the gap and its proposed fix
   first.
6. **Guarantees come from resources, not axioms.** Facts such as "two boxes
   never share an allocation" follow from what each value owns, since owning
   something excludes every other owner. They are not kernel rules about a
   type, so code outside a language's safe subset, unsafe Rust or a foreign
   call, can be checked against the same interface.
7. **Keep program names and proof names distinct.** Preserve library types,
   names, and call signatures as the source language exposes them. Define
   resources and proof-only helpers whose meaning comes from that library in
   `click::<language>::<library>`, such as `click::c::stdio` for C format
   rendering. Define queries on ghost state as module-level specification
   functions. Keep operations with language-independent meanings, such as
   byte equality, in shared specification modules. In sidecar examples,
   prefer a selective import of the proof names the example uses.

## Adding an interface

1. Write the contract, and the type's ownership resource if it owns memory, in
   the library file for its language: `library/c/`, `library/cpp/` or
   `library/rust/`. State observable effects only (principle 2).
2. Map the call to it in the front end's name table:
   `src/languages/cpp/standard_library.rs` or
   `src/languages/rust/standard_library.rs`, or the C front end's
   `library_contract_module`. Add nothing else to the front end (principle 4).
3. Add its inventory item and its entry in the
   [library reference](../reference/library/index.md), and name its file in
   its family's row of [trust](trust.md#library-interfaces).
4. Add a verified use: a test or fixture that calls it and verifies, and that
   is refused when a precondition is not met.
5. If a step above cannot be done with today's contracts, stop at principle 5.

A pure specification module, `click::list` or `click::nat`, is not an
interface: it is ordinary Click with no library behind it. Adding one follows
the [feature playbook](../internals/feature-playbook.md#adding-standard-library-definitions).

## Where the implementation departs from this

These front-end special cases predate the principles. Each is debt, unless
noted, and a new interface must not copy one.

| Language | Special case | Where | What replaces it |
| --- | --- | --- | --- |
| Rust | `Box::new` and a box's drop are importer steps, `BoxNew` and `BoxFree`; each proof writes its box's ownership resource by hand | `src/languages/rust/charon.rs`, `src/languages/rust/lowering/moves.rs` | `Box`'s contracts and ownership resource in `library/rust/` |
| Rust | `Option::take` is rewritten into the move its implementation makes | `src/languages/rust/charon/option_take.rs` | One generic `Option::take<T>` contract |
| Rust | `?` checks the library's own `Try` and `FromResidual` impls, then rewrites them into the `match` they define | `src/languages/rust/charon/option_try.rs`, `src/languages/rust/charon/result_try.rs` | Contracts of `branch` and `from_residual` |
| Rust | `Range`, `slice::Iter`, `ChunksExact` and `Enumerate` are importer statements (`RangeNext`, `ChunkNext`, ...) over the iterators' fields | `src/languages/rust/charon/`, `src/languages/rust/lowering/` | Contracts of each iterator's `next` |
| C++ | `std::span` and `std::array` contracts read their objects' layout | `library/cpp/span.click`, `library/cpp/array.click` | Contracts over each object's logical state ([C++ standard library](../reference/cli/import.md#c-standard-library)) |
| C | The allocator family is built into the C front end and the kernel | `src/languages/c/` | Justified: allocation is part of C's memory model, not a library call |
| C | Literal formats in `snprintf`, `printf` and `fprintf` select a fixed-arity contract | `src/languages/c/formatted_output.rs`, `library/c/stream_output.click.in` | Justified while formats are checked by the C front end. The stream transition is an ordinary Click contract. |
| C | The thread runtime is a selected specification in Rust code | `src/languages/c/thread_runtime.rs` | Justified: it models the runtime, not one function |

A gap is a missing feature in an interface that follows the principles:

- `Vec<T>` is an abstract value with no memory behind it, so its interface
  cannot describe a borrow into the vector, `&mut v[i]`, `iter_mut` or
  `as_mut_slice`. Giving it a buffer owned through its resource closes the
  gap when a program needs those borrows.
