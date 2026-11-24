# Explicit explicit preservation proof across two stores

```c filename=fields.c
struct cursor { int pos; int len; int *data; };
void copy_pos(struct cursor *target, struct cursor *source) {
    target->pos = source->pos;
    target->pos = source->len;
}
```

```click
import click::separation;
verifying "fields.c";

void copy_pos(struct cursor *target, struct cursor *source) {
    owns *target;
    views *source;
    requires separate(memory(*target), memory(*source));
} by {
    have contains(memory(*target), memory(target->pos)) by { normalize(); }
    have contains(memory(*source), memory(source->data)) by { normalize(); }
    have separate(memory(target->pos), memory(source->data)) by {
        apply(separation::separate_restrict(memory(*target), memory(*source),
            memory(target->pos), memory(source->data)));
    }
    have contains(memory(*source), memory(*source)) by { apply(separation::contains_refl(memory(*source))); }
    have separate(memory(target->pos), memory(*source)) by {
        apply(separation::separate_restrict(memory(*target), memory(*source), memory(target->pos), memory(*source)));
    }
    mark before;
    step() by { close(); }
    mark after;
    have separate(statement(0).footprint, memory(source->data)) by {
        close() using { separate(memory(target->pos), memory(source->data)); };
    }
    have source->data == at(before, source->data) by {
        preserve(memory(source->data), statement(0));
    }
    step() by { close(); }
    mark final;
    have separate(statement(1).footprint, memory(source->data)) by {
        close() using { separate(memory(target->pos), memory(source->data)); };
    }
    have source->data == at(before, source->data) by {
        have source->data == at(after, source->data) by {
            preserve(memory(source->data), statement(1));
        }
        rewrite(source->data, at(after, source->data));
        close();
    }
    step();
    close();
    close(); close(); close();
}
```

```expect
pass
```
