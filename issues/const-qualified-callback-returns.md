# Preserve const-qualified callback returns

## Violated invariant

Direct C calls now retain pointee const on return values through C prototypes,
Click signatures, external contracts, call result storage, and return binding.
The same view cannot yet be expressed for callback returns. Qualified callback
declarations and addresses of known const-returning functions are deliberately
rejected; the kernel also rejects indirect calls to const-returning targets.
Do not remove these checks without modeling qualification in callback identity.

## Intended regression

Use unchanged C with `const int *view(int *p) { return p; }` and a callback
declared `const int *(*f)(int *)`. Prove that a call through `f` returns the
same address and permits reads, but cannot initialize a mutable pointee view,
write through the result, or satisfy a mutable-return callback signature.
Cover known function addresses, abstract named-contract calls, callback fields,
and cross-file prototypes. Keep direct const-return and unsigned-char regressions.

## Acceptance criteria

- Callback identity retains return qualification without collisions; use an
  exact encoding with validated capacity, not a truncated or probabilistic key.
- C and Click boundary checks preserve return and parameter qualification.
- Actual and symbolic indirect-call results retain const through temporaries
  and caller bindings; the kernel independently rejects const-discard paths.
- Replace the deliberate rejection regressions only when positive and negative
  kernel/fixture coverage and `scripts/check.sh` pass.

Signed-byte types remain tracked in `signed-byte-integers.md`; alternative char
signedness and compiler configurations remain in `multiple-compilers.md`.
