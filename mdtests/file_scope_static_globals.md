# File-scope static globals are private to each translation unit

File-scope `static` objects with the same C spelling in different source files
must have independent storage. Their owning functions can still authorize and
describe the one-cell state through ordinary contracts.

```c filename=alpha.c
static int32 counter = 1;

int32 increment_alpha() {
    counter = counter + 1;
    return counter;
}

int32 increment_alpha_again() {
    counter = counter + 1;
    return counter;
}
```

```c filename=beta.c
static int32 counter = 10;

int32 increment_beta() {
    counter = counter + 1;
    return counter;
}
```

```c filename=runner.c
int32 increment_alpha();
int32 increment_alpha_again();
int32 increment_beta();

int32 run() {
    int32 alpha;
    int32 alpha_again;
    int32 beta;
    alpha = increment_alpha();
    alpha_again = increment_alpha_again();
    beta = increment_beta();
    return alpha + alpha_again + beta;
}
```

```click
verifying "alpha.c";
verifying "beta.c";
verifying "runner.c";

int32 increment_alpha() {
    mutable &counter[0..1] by auto;
    ensures result == old(counter) + 1 by auto;
    ensures counter == old(counter) + 1 by auto;
}

int32 increment_alpha_again() {
    mutable &counter[0..1] by auto;
    ensures result == old(counter) + 1 by auto;
    ensures counter == old(counter) + 1 by auto;
}

int32 increment_beta() {
    mutable &counter[0..1] by auto;
    ensures result == old(counter) + 1 by auto;
    ensures counter == old(counter) + 1 by auto;
}

int32 run() {
    ensures result == 16 by auto;
}
```

```expect
pass
```
