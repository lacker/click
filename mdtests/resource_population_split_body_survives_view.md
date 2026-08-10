# Split population bodies remain canonical across opaque views

An opaque mutation may split an active object body into field ranges. A later
viewing call must recognize those ranges as the one exposed body of the still
folded population, rather than trying to compose a duplicate whole object.

```c filename=resource_population_split_wrap.c
struct pair {
    int32 left;
    int32 right;
};

void wrap_pair(struct pair* pair) {
}
```

```c filename=resource_population_split_set.c
struct pair {
    int32 left;
    int32 right;
};

void set_left(struct pair* pair) {
    pair->left = 7;
}
```

```c filename=resource_population_split_read.c
struct pair {
    int32 left;
    int32 right;
};

int32 read_right(struct pair* pair) {
    return pair->right;
}
```

```c filename=resource_population_split_pipeline.c
struct pair {
    int32 left;
    int32 right;
};

void split_body_pipeline(struct pair* pair) {
    wrap_pair(pair);
    set_left(pair);
    read_right(pair);
}
```

```click
resource wrapper(pair: struct pair*) {
    owns object(pair);
}

verifying "resource_population_split_wrap.c";
verifying "resource_population_split_set.c";
verifying "resource_population_split_read.c";
verifying "resource_population_split_pipeline.c";

void wrap_pair(struct pair* pair) {
    consumes object(pair);
    produces wrapper(pair);
} by {
    execute();
    fold(wrapper(pair));
    simp();
}

void set_left(struct pair* pair) {
    owns wrapper(pair);
    mutable pair->left;
} by {
    open(wrapper(pair)) {
        execute();
        frame();
        simp();
    }
}

int32 read_right(struct pair* pair) {
    views wrapper(pair);
    immutable;

    ensures result == pair->right by auto;
}

void split_body_pipeline(struct pair* pair) {
    owns object(pair);
    mutable object(pair);
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
