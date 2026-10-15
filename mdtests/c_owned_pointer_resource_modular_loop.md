# An owning C pointer resource survives a modular loop back edge

The service step writes through an owned pointer field without changing the
allocation or the owned resource. Retain the original service step and loop;
learning access facts during the call must not count as a lifetime transition.

```c filename=service_step.c
struct service {
    int32 phase;
    int32* cell;
};

int32 service_step(struct service* owner) {
    if (owner->phase == 0) {
        owner->phase = 1;
    } else {
        owner->phase = 0;
    }
    owner->cell[0] = owner->phase;
    return owner->phase;
}
```

```c filename=service_run.c
struct service {
    int32 phase;
    int32* cell;
};

int32 service_run(struct service* owner) {
    int32 status;
    while (1) {
        status = service_step(owner);
    }
    return status;
}
```

```click
resource service(owner: struct service*) {
    owns *owner;
    owns owner->cell[0..1];
    fact 0 <= owner->phase;
    fact owner->phase <= 1;
    fact owner->cell[0] == owner->phase;
    fact separate(memory(*owner), memory(owner->cell[0..1]));
}

verifying "service_step.c";
verifying "service_run.c";

int32 service_step(struct service* owner) {
    owns service(owner);

    ensures result == owner->phase;
    ensures owner->cell == old(owner->cell);
    ensures 0 <= owner->phase;
    ensures owner->phase <= 1;
    ensures owner->cell[0] == owner->phase;
} by {
    unfold(service(owner));
    branch ensuring {
        fact 0 <= owner->phase;
        fact owner->phase <= 1;
        fact owner->cell == old(owner->cell);
        fact separate(memory(*owner), memory(owner->cell[0..1]));
        owns *owner;
        owns owner->cell[0..1];
    } then {
        step();
        have owner->cell == old(owner->cell) by auto;
    } else {
        step();
        have owner->cell == old(owner->cell) by auto;
    }
    step();
    fold(service(owner));
    observe(service(owner));
    step();
    simp();
}

int32 service_run(struct service* owner) diverges {
    owns service(owner);
} by {
    step();
    loop diverges {
        invariant 0 <= owner->phase;
        invariant owner->phase <= 1;
        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    simp();
}
```

```expect
pass
```
