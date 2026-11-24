# Restrict separation after an explicit address equality

```click
import click::separation;
theorem selected(A: Resource, p: int32*, q: int32*, i: int32, cap: int32) {
    requires p == q;
    requires separate(A, memory(p[0..cap]));
    requires 0 <= i;
    requires i < cap;
    ensures separate(A, memory(q[i])) by {
        have separate(A, memory(q[0..cap])) by {
            rewrite(q, p);
            close();
        }
        have i <= 2147483646 by { close() using { i < cap; }; }
        have defined(i + 1) by { close() using { 0 <= i; i <= 2147483646; }; }
        have i <= ((i + 1) as int32) by { close() using { 0 <= i; i < cap; }; }
        have ((i + 1) as int32) <= cap by { close() using { 0 <= i; i < cap; }; }
        have contains(memory(q[0..cap]), memory(q[i..i+1])) by {
            apply(separation::contains_subrange(q, 0, cap, i, i+1));
        }
        have contains(A, A) by { apply(click::separation::contains_refl(A)); }
        have separate(A, memory(q[i..i+1])) by {
            apply(separation::separate_restrict(A, memory(q[0..cap]), A, memory(q[i..i+1])));
        }
        have contains(memory(q[i..i+1]), memory(q[i])) by { normalize(); }
        apply(separation::separate_restrict(A, memory(q[i..i+1]), A, memory(q[i])));
    }
}
```

```expect
pass
```
