# A guarded resource cannot silently use ordinary resource semantics

`guarded_by` is a resource-body declaration of the C mutex field that guards
the whole body. Until Click has a checked mutex protocol, verification refuses
it rather than treating the body as an ordinary folded resource.

```c filename=guarded_resource_requires_mutex_protocol.c
struct counter { int mu; int value; };

int read_counter(struct counter *counter) {
    return counter->value;
}
```

```click
resource counter_state(counter: struct counter*) {
    guarded_by counter->mu;
    owns counter->value;
}

verifying "guarded_resource_requires_mutex_protocol.c";

int32 read_counter(struct counter *counter) {
    owns counter_state(counter);
} by {
    execute();
    simp();
}
```

```expect
fail: resource `counter_state` declares `guarded_by`, but the modeled mutex protocol is not implemented
```
