# file-scope static arrays remain private to their translation units

Same-named file-scope `static` arrays in different source files have separate
stable storage, just like same-named scalar statics.

```c filename=alpha.c
static int32 values[2] = {1, 2};

int32 alpha() {
    values[0] = values[0] + 1;
    return values[0] + values[1];
}
```

```c filename=beta.c
static int32 values[2] = {10, 20};

int32 beta() {
    values[0] = values[0] + 1;
    return values[0] + values[1];
}
```

```c filename=runner.c
int32 alpha();
int32 beta();

int32 run() {
    int32 first = alpha();
    int32 second = beta();
    return first + second;
}
```

```click
verifying "alpha.c" as alpha_file;
verifying "beta.c" as beta_file;
verifying "runner.c";

int32 alpha() {
    owns values[0..2];
    requires values[0] > -1000 and values[0] < 1000 and values[1] > -1000 and values[1] < 1000;
    ensures result == old(values[0]) + old(values[1]) + 1 by auto;
    ensures result == values[0] + values[1] by auto;
}

int32 beta() {
    owns values[0..2];
    requires values[0] > -1000 and values[0] < 1000 and values[1] > -1000 and values[1] < 1000;
    ensures result == old(values[0]) + old(values[1]) + 1 by auto;
    ensures result == values[0] + values[1] by auto;
}

int32 run() {
    owns alpha_file::values[0..2];
    owns beta_file::values[0..2];
    requires alpha_file::values[0] == 1;
    requires alpha_file::values[1] == 2;
    requires beta_file::values[0] == 10;
    requires beta_file::values[1] == 20;
    requires alpha_file::values[0] > -1000;
    requires alpha_file::values[0] < 1000;
    requires alpha_file::values[1] > -1000;
    requires alpha_file::values[1] < 1000;
    requires beta_file::values[0] > -1000;
    requires beta_file::values[0] < 1000;
    requires beta_file::values[1] > -1000;
    requires beta_file::values[1] < 1000;
} by {
    have alpha_file::values[0] == 1 by simp;
    have alpha_file::values[1] == 2 by simp;
    have beta_file::values[0] == 10 by simp;
    have beta_file::values[1] == 20 by simp;
    have alpha_file::values[0] > -1000 by simp;
    have alpha_file::values[0] < 1000 by simp;
    have alpha_file::values[1] > -1000 by simp;
    have alpha_file::values[1] < 1000 by simp;
    have beta_file::values[0] > -1000 by simp;
    have beta_file::values[0] < 1000 by simp;
    have beta_file::values[1] > -1000 by simp;
    have beta_file::values[1] < 1000 by simp;
    execute();
    simp();
}
```

```expect
pass
```
