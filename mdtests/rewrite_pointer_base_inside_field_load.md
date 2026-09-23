# Rewrite a pointer base inside a field load

`rewrite` uses one exact pointer equality, including when a field load names
the pointer with a constant byte displacement. The load keeps its memory
snapshot. The matched resource's `kid` and the C field `p->kid` have different
symbolic block spellings, so this exercises more than offset equality within
one block.

```c filename=rewrite_pointer_base_inside_field_load.c
struct child { int32 payload; };
struct holder { struct child* kid; };

void inspect(struct holder* p) {}
```

```click
spec enum Link { Linked(struct child*) }

resource holder(p: struct holder*) {
    field link: Link;
    match link {
        Link::Linked(kid) => {
            owns &p->kid;
            owns &kid->payload;
            fact p->kid == kid;
        },
    }
}

verifying "rewrite_pointer_base_inside_field_load.c";

void inspect(struct holder* p) {
    owns h: holder(p);
} by {
    match h.link {
        Link::Linked(kid) => {
            unfold(h);
            have p->kid == kid by { simp(); }
            have kid->payload == p->kid->payload by {
                rewrite(p->kid == kid);
                normalize();
            }
            let h = fold(holder(p), { link: Link::Linked(kid) });
            execute();
            simp();
        },
    }
}
```

```expect
pass
```
