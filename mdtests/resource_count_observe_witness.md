# observe exposes resource-count lower bounds

`observe` can name the count evidence carried by owned declared resources. It
does not consume the resource. An omitted quantity means one; an explicit
quantity proves the corresponding lower bound without enumerating units.

```c filename=observe_one_permit.c
struct owner {
    int32 value;
};

void observe_one_permit(struct owner* owner) {
}
```

```c filename=observe_many_permits.c
struct owner {
    int32 value;
};

void observe_many_permits(struct owner* owner, int32 amount) {
}
```

```click
resource permit(owner: struct owner*) {
    views object(owner);
}

verifying "observe_one_permit.c";
verifying "observe_many_permits.c";

void observe_one_permit(struct owner* owner) {
    owns object(owner);
    owns permit(owner);

    ensures 1 <= count(permit(owner));
} by {
    observe(permit(owner));
    execute();
    simp();
}

void observe_many_permits(struct owner* owner, int32 amount) {
    requires 0 <= amount;
    owns object(owner);
    owns amount of permit(owner);

    ensures amount <= count(permit(owner));
} by {
    observe(amount of permit(owner));
    execute();
    simp();
}
```

```expect
pass
```
