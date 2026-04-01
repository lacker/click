# Click Design

This document records the current design direction for `click`.

## Goal

`click` is meant to become:

- a reasonable language to program in
- a language where programs are easy to inspect and transform as data
- a language where transformations can carry machine-checkable correctness arguments
- a language where the checking and proving infrastructure can be written in the language itself

## The Kernel

The heart of the Click kernel is a few trusted Rust things.

* A "list" representation. This represents code, data, and types. Lispy.

* An "eval" function. This evaluates code.

* A "typecheck" function. This verifies that a particular thing adheres to a particular type.

* A powerful enough typesystem that we can implement proofs via typechecking.

There are perhaps some other details. But this is the idea.

Everything else, we should be able to write on top of the kernel.

## Baby Steps

Once we have the kernel written, we need to do some basic stuff on top of the kernel.

* Implement "eval" and "typecheck" in Click itself.
It's not that we will use these, exactly. But it's a demonstration that the kernel has sufficient power.

* Implement some basic types, typeclasses, type-ish things.
Bool
Nat
List<T>
"Total function"
Dependent types, like perhaps Vec<T, n>
Container
Iterator

* Implement some basic proofs
Reversing a list twice gives the same thing
Addition is commutative and associative

## Current Kernel

I'm not happy with the current kernel. We need to rethink and rework.

The current kernel has:

- `quote`
- `if`
- `atom`
- `atom_eq`
- `car`
- `cdr`
- `cons`
- `lambda`
- `stack`
- `nil`
- `true`
- `false`

Ordinary symbols do not self-evaluate.

### Closures

The current prototype uses proper lexical closures.

Conceptually:

```lisp
(lambda body)  ==>  (closure body env)
```

and application means:

```lisp
(apply (closure body env) arg)
  = evaluate body (cons arg env)
```

In the prototype, closures are explicit list data:

```lisp
(closure body env)
```

Malformed closures are allowed as ordinary data, but applying them is an
error.

I feel like closures are a bad design, but I'm not entirely sure why.

### `stack`

The current prototype also exposes the lexical environment through `stack`.

Examples:

```lisp
((lambda stack) 'a)                  ; => (a)
((lambda (car stack)) 'a)            ; => a
(((lambda (lambda (car (cdr stack)))) 'a) 'b)  ; => a
```

I feel like this is a bad design too. Just super ugly. Better to just bite the bullet and having some sort of names and bindings.
