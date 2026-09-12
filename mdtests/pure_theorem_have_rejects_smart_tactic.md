# a `have` inside a theorem names the smart tactic it cannot take

A pure theorem's nested `have` is checked from a certificate, and a certificate
holds simple steps only, so its body must be an explicit simple proof. Writing
`simp()` there is a real mistake — `simp` searches, and a search leaves nothing
to check — but the refusal used to print the certificate's Rust debug form,
`CertificateError { tactic_class: Smart(Simp), path: [Tactic(0)] }`, which names
neither the rule nor the spelling to write instead. It now says which smart
tactic was used and where it sits, in the spelling the author wrote.

The same nested `have` with `normalize() using { ... }` is the working form; it
is what every theorem in [`examples/rbtree-model`](../examples/rbtree-model/README.md)
writes.

```c filename=symmetry.c
int nothing(void) { return 0; }
```

```click
verifying "symmetry.c";

theorem pointer_disequality_symmetry(a: int32*, b: int32*) {
    requires a != b;

    ensures 1 == 1 by {
        have b != a by { simp(); }
        normalize();
    }
}

int nothing() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: a `have` inside a theorem takes an explicit simple proof, and this one uses smart tactic `simp` at tactic 0
```
