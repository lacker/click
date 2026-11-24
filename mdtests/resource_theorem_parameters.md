# Resource descriptors as theorem arguments

```c filename=fields.c
struct cursor { int pos; int len; int *data; };
void copy_pos(struct cursor *target, struct cursor *source) {
    target->pos = source->pos;
}
```

```click
import click::separation;
verifying "fields.c";

theorem restrict_again(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b) by {
        apply(separation::separate_restrict(A, B, a, b));
    }
}

void copy_pos(struct cursor *target, struct cursor *source) {
    owns *target;
    views *source;
    requires separate(memory(*target), memory(*source));
} by {
    have contains(memory(*target), memory(target->pos)) by { normalize(); }
    have contains(memory(*source), memory(source->data)) by { normalize(); }
    have separate(memory(target->pos), memory(source->data)) by {
        apply(restrict_again(memory(*target), memory(*source),
            memory(target->pos), memory(source->data)));
    }
    have contains(memory(*source), memory(*source)) by { apply(separation::contains_refl(memory(*source))); }
    have separate(memory(target->pos), memory(*source)) by {
        apply(separation::separate_restrict(memory(*target), memory(*source), memory(target->pos), memory(*source)));
    }
    step() by { close(); }
    step();
    close();
    close(); close(); close();
}
```

```expect
pass
```
