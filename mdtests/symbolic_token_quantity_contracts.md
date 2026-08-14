# Symbolic abstract-resource quantities cross opaque contracts

A runtime-sized abstract-resource quantity is one algebraic resource entry. An
opaque pass-through and consumer transfer the symbolic amount without
enumerating its units or manufacturing authority.

```c filename=symbolic_token_forward.c
void forward(int32 amount) {
}
```

```c filename=symbolic_token_spend.c
void spend(int32 amount) {
}
```

```c filename=symbolic_token_pipeline.c
void quantity_pipeline(int32 amount) {
    forward(amount);
    spend(amount);
}
```

```click
abstract resource permit();

verifying "symbolic_token_forward.c";
verifying "symbolic_token_spend.c";
verifying "symbolic_token_pipeline.c";

void forward(int32 amount) {
    requires 0 <= amount;
    owns amount of permit();
} by auto;

void spend(int32 amount) {
    requires 0 <= amount;
    consumes amount of permit();
}

void quantity_pipeline(int32 amount) {
    requires 0 <= amount;
    consumes amount of permit();
} by auto;
```

```expect
pass
```
