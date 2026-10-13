# A `long` global declared `long long` in another file is refused

Linking a `long` definition with a `long long` declaration of the same object
is undefined behavior (C11 6.2.7p2): the declarations' types are not
compatible, although they share a representation. Click links the two
translation units and refuses the conflict.

```c filename=data.c
long total = 3;
```

```c filename=main.c
extern long long total;
int run(int value) { return value; }
```

```click
verifying "data.c";
verifying "main.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: conflicting declarations for global `total`
```
