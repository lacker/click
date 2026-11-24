# A wide-index store supplies its borrow separation explicitly

```c filename=wide_index_write.c
struct E { unsigned long n; };
struct S { struct E e; };
void set_at(int *p, const struct S *s, unsigned long i, int v) { p[i] = v; }
```

```click
verifying "wide_index_write.c";
void set_at(int32* p, const struct S* s, uint64 i, int32 v) {
    views s->e.n;
    owns p[0..s->e.n];
    requires i < s->e.n;
    ensures p[i] == v;
} by {
    have 0u64 <= i by { close(); }
    have contains(memory(p[0u64..s->e.n]), memory(p[i])) by {
        apply(click::separation::contains_element(p, 0u64, s->e.n, i));
    }
    have contains(memory(s->e.n), memory(s->e.n)) by {
        apply(click::separation::contains_refl(memory(s->e.n)));
    }
    have separate(memory(p[i]), memory(s->e.n)) by {
        apply(click::separation::separate_restrict(memory(p[0u64..s->e.n]), memory(s->e.n), memory(p[i]), memory(s->e.n)));
    }
    step_until(function.exit);

}
```

```expect
pass
```
